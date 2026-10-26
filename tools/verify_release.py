#!/usr/bin/env python3
"""Check the release hashes and their agreement with the recorded proof audit."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    manifest = json.loads((ROOT / "release-manifest.json").read_text())
    for name, expected in manifest["files"].items():
        path = ROOT / name
        require(path.is_file(), "Missing release file: " + name)
        require(digest(path) == expected, "Changed release file: " + name)
    final = json.loads((ROOT / "verification/final-audit.json").read_text())
    published = set((ROOT / "lean").rglob("*.lean"))
    checked = set()
    for module, expected in final["local_source_sha256"].items():
        path = (ROOT / "lean" / Path(*module.split("."))).with_suffix(".lean")
        require(digest(path) == expected, "Lean audit mismatch: " + module)
        checked.add(path)
    require(published == checked, "Published Lean files differ from the checked closure")
    for name, key in [("lake-manifest.json", "manifest_sha256"),
                      ("lean-toolchain", "toolchain_sha256")]:
        require(digest(ROOT / "lean" / name) == final[key], "Changed pin: " + name)
    paper = json.loads((ROOT / "verification/manuscript.json").read_text())
    require(digest(ROOT / paper["pdf"]) == paper["pdf_sha256"], "PDF audit mismatch")
    for name, expected in paper["sources"].items():
        require(digest(ROOT / "paper" / name) == expected, "TeX audit mismatch: " + name)
    independent = final["independent_verification"]
    receipt = ROOT / independent["receipt"]
    require(digest(receipt) == independent["receipt_sha256"], "NanoDa receipt mismatch")
    nano = json.loads(receipt.read_text())
    require(nano["check"]["exit_code"] == 0, "NanoDa did not pass")
    require(set(nano["export"]["axioms"]) == {"propext", "Classical.choice", "Quot.sound"},
            "Unexpected exported axioms")
    require(set(nano["export"]["targets_with_proof_terms"]) == set(nano["targets"]),
            "An exported target lacks its recorded proof term")
    print(f"Verified {len(manifest['files'])} release files, {len(checked)} checked Lean sources, "
          "the manuscript, dependency pins, and the successful NanoDa receipt.")
    print("This checks the recorded file identities; it does not rerun Lean or NanoDa.")


if __name__ == "__main__":
    main()

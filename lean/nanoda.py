#!/usr/bin/env python3
"""Export the final proof dependencies and check them with installed NanoDa.

The export contains proof terms, including the imported declarations used
by the targets. Only the three recorded axioms are permitted. Large exports
and logs stay in the existing external project workspace.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import subprocess
import sys

sys.dont_write_bytecode = True
import build
import build_guard as guard

MODULE = "Quantitative.MainTheorems"
TARGETS = [
    "CoefficientTwoPrecision.finite_covering_word",
    "CoefficientTwoPrecision.shortest_length_error",
    "CoefficientTwoPrecision.shortest_length_asymptotic",
]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def inspect_export(path):
    names = {0: ""}
    counts = {}
    axioms = []
    targets = {}
    metadata = None
    with path.open() as f:
        for line in f:
            item = json.loads(line)
            if "meta" in item:
                metadata = item["meta"]
            if "in" in item:
                data = item.get("str", item.get("num"))
                pre = names[data["pre"]]
                suffix = str(data.get("str", data.get("i")))
                names[item["in"]] = pre + ("." if pre else "") + suffix
            for kind in ["axiom", "def", "thm", "opaque", "inductive", "constructor", "recursor", "quot"]:
                if kind not in item:
                    continue
                counts[kind] = counts.get(kind, 0) + 1
                data = item[kind]
                name = names.get(data.get("name"))
                if kind == "axiom":
                    axioms.append(name)
                if name in TARGETS:
                    if kind != "thm" or "value" not in data:
                        raise RuntimeError("Target was not exported with its proof: " + name)
                    targets[name] = {"kind": kind, "type": data["type"], "value": data["value"]}
    if set(targets) != set(TARGETS):
        raise RuntimeError("Export omitted a final target")
    if not set(axioms) <= set(AXIOMS):
        raise RuntimeError("Unexpected exported axioms: " + str(axioms))
    return {"metadata": metadata, "declaration_counts": counts,
            "axioms": axioms, "targets_with_proof_terms": targets}


def export_worker(output):
    command = [str(build.COMPILER.parent / "leanexport"), MODULE, "--", *TARGETS]
    with Path(output).open("wb") as f:
        result = subprocess.run(command, stdout=f)
    raise SystemExit(result.returncode)


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--export-worker":
        export_worker(sys.argv[2])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reuse-export", type=Path,
                        help="Reuse a previously successful export after verifying its recorded hashes")
    args = parser.parse_args()
    packages = build.check_pins()
    workspace = build.workspace()
    with guard.compiler_slot(workspace.parent / "compile.lock", wait_seconds=0):
        guard.require_free_disk(workspace)
        final = json.loads((build.RECEIPTS / "final-audit.json").read_text())
        for module, expected in final["local_source_sha256"].items():
            source = (build.ROOT / Path(*module.split("."))).with_suffix(".lean")
            if digest(source) != expected:
                raise RuntimeError("Source changed since final audit: " + module)
        obj = (workspace / ".lake/build/lib/lean" / Path(*MODULE.split("."))).with_suffix(".olean")
        stamp = json.loads(obj.with_suffix(".build.json").read_text())
        if stamp["exit_code"] != 0 or digest(obj) != stamp["olean_sha256"]:
            raise RuntimeError("Final checked object changed")
        attempt = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        directory = workspace / "nanoda" / attempt
        directory.mkdir(parents=True)
        env = os.environ.copy()
        env["PATH"] = str(build.COMPILER.parent) + os.pathsep + env.get("PATH", "")
        env["LEAN_NUM_THREADS"] = "1"
        env["RAYON_NUM_THREADS"] = "1"
        env["LEAN_PATH"] = os.pathsep.join([str(workspace / ".lake/build/lib/lean")] +
            [str(Path(p["path"]) / ".lake/build/lib/lean") for p in packages])
        checker = build.COMPILER.parent / "nanoda_bin"
        exporter = build.COMPILER.parent / "leanexport"
        receipt = {
            "module": MODULE, "targets": TARGETS,
            "scope": "Final target proof terms and their transitive declaration dependencies, including imported proofs",
            "compiler": stamp["version"], "module_olean_sha256": digest(obj),
            "exporter": str(exporter), "exporter_sha256": digest(exporter),
            "checker": str(checker), "checker_sha256": digest(checker),
            "checker_version": "nanoda_bin 0.4.19 (installed binary --help)",
            "permitted_axioms": AXIOMS, "workspace": str(directory),
        }
        receipt_path = build.RECEIPTS / "nanoda" / (attempt + ".json")
        if args.reuse_export:
            prior = json.loads(args.reuse_export.read_text())
            for key in ["module", "targets", "compiler", "module_olean_sha256", "exporter_sha256"]:
                if prior[key] != receipt[key]:
                    raise RuntimeError("Export provenance changed: " + key)
            output = Path(prior["export"]["path"])
            if prior["export"]["exit_code"] != 0 or digest(output) != prior["export"]["sha256"]:
                raise RuntimeError("Export has no matching successful hash record")
            receipt["export"] = prior["export"]
            receipt["reused_export_receipt"] = str(args.reuse_export.resolve())
        else:
            partial = directory / "proof.ndjson.partial"
            export_command = ["/usr/bin/nice", "-n", "10", sys.executable,
                              str(Path(__file__).resolve()), "--export-worker", str(partial)]
            print("Exporting the final theorems and their proof dependencies.", flush=True)
            export = guard.run_checked(export_command, cwd=workspace, env=env,
                                      log_path=directory / "export.log", timeout_seconds=120)
            receipt["export"] = {"command": export_command,
                "exporter_command": [str(exporter), MODULE, "--", *TARGETS],
                "exit_code": export.returncode, "resource_report": export.resource_report}
            build.write_json(receipt_path, receipt)
            if export.returncode != 0:
                print(export.stdout[-10000:])
                raise SystemExit(export.returncode)
            output = directory / "proof.ndjson"
            os.replace(partial, output)
            receipt["export"].update({"path": str(output), "bytes": output.stat().st_size,
                                      "sha256": digest(output), **inspect_export(output)})
        config = {"export_file_path": str(output), "use_stdin": False,
                  "permitted_axioms": AXIOMS, "unpermitted_axiom_hard_error": True,
                  "unsafe_permit_all_axioms": False, "nat_extension": True,
                  "string_extension": True, "num_threads": 1,
                  "pp_declars": TARGETS, "pp_to_stdout": False,
                  "pp_output_path": str(directory / "target-statements.txt"),
                  "print_success_message": True}
        config_path = directory / "nanoda-config.json"
        Path(config["pp_output_path"]).touch()
        build.write_json(config_path, config)
        receipt["config"] = config
        build.write_json(receipt_path, receipt)
        print("Export complete:", output.stat().st_size, "bytes; running NanoDa.", flush=True)
        command = ["/usr/bin/nice", "-n", "10", str(checker), str(config_path)]
        checked = guard.run_checked(command, cwd=workspace, env=env,
                                   log_path=directory / "nanoda.log", timeout_seconds=120)
        receipt["check"] = {"command": command, "exit_code": checked.returncode,
                            "resource_report": checked.resource_report,
                            "log": str(directory / "nanoda.log"), "output": checked.stdout}
        receipt["completed_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        build.write_json(receipt_path, receipt)
        if checked.returncode == 0:
            text = (directory / "target-statements.txt").read_text()
            (build.RECEIPTS / "nanoda" / (attempt + "-statements.txt")).write_text(text)
        print(checked.stdout[-10000:])
        print("NanoDa exit status:", checked.returncode)
        print("Receipt:", receipt_path)
        raise SystemExit(checked.returncode)


if __name__ == "__main__":
    main()

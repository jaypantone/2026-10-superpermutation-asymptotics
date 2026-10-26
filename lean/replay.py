#!/usr/bin/env python3
"""Replay one checked module with the matching Lean 4.35.0 kernel.

Ordinary replay checks the module's declarations against its imported
environment. --fresh also replays the imported declarations from an empty
environment. This is a second kernel pass, not an external proof checker.
"""
from pathlib import Path
import argparse
import datetime
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
import build
import build_guard as guard


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module")
    parser.add_argument("--fresh", action="store_true")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*", args.module):
        raise RuntimeError("Invalid module name")
    packages = build.check_pins()
    target = build.workspace()
    with guard.compiler_slot(target.parent / "compile.lock", wait_seconds=0):
        guard.require_free_disk(target)
        relative = Path(*args.module.split("."))
        source = (build.ROOT / relative).with_suffix(".lean")
        obj = (target / ".lake/build/lib/lean" / relative).with_suffix(".olean")
        stamp = json.loads(obj.with_suffix(".build.json").read_text())
        if stamp["exit_code"] != 0 or stamp["source_sha256"] != build.digest(source):
            raise RuntimeError("Current source has not passed compilation")
        if stamp["olean_sha256"] != build.digest(obj):
            raise RuntimeError("Checked object hash changed")
        env = os.environ.copy()
        env["PATH"] = str(build.COMPILER.parent) + os.pathsep + env.get("PATH", "")
        env["LEAN_NUM_THREADS"] = "1"
        env["LEAN_PATH"] = os.pathsep.join([str(target / ".lake/build/lib/lean")] +
            [str(Path(p["path"]) / ".lake/build/lib/lean") for p in packages])
        version = subprocess.check_output([str(build.COMPILER), "--version"], text=True).strip()
        if version != stamp["version"]:
            raise RuntimeError("Compiler version differs from the checked object")
        attempt = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        log = target / "logs" / (args.module + "-replay-" + attempt + ".log")
        command = ["/usr/bin/nice", "-n", "10", str(build.COMPILER.parent / "leanchecker"), "-v"]
        if args.fresh:
            command.append("--fresh")
        command.append(args.module)
        result = guard.run_checked(command, cwd=target, env=env, log_path=log, timeout_seconds=120)
        receipt = {
            "module": args.module, "version": version, "command": command,
            "cwd": str(target), "source_sha256": build.digest(source),
            "olean_sha256": build.digest(obj), "fresh": args.fresh,
            "scope": "Module and imported declarations" if args.fresh else "Module declarations against imported environment",
            "checker": "Matching Lean kernel replay; not an external verifier",
            "exit_code": result.returncode, "log": str(log),
            "completed_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "resource_report": result.resource_report,
        }
        build.write_json(build.RECEIPTS / "replay" / (args.module + "-" + attempt + ".json"), receipt)
        print(result.stdout[-10000:])
        print("Replay exit status:", result.returncode)
        raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()

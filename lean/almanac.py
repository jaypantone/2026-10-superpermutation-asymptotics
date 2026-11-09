#!/usr/bin/env python3
"""Check the Superpermutation Almanac submission modules.

The released modules are not recompiled. Each one in the import closure of
AlmanacSolution must already have a successful checked object whose recorded
source hash equals the file in lean/. The runner then compiles AlmanacDefs,
AlmanacAdapter and AlmanacSolution from the repository root under the same
guard as build.py, prints the axioms of the submitted statements, exports
them with their proof dependencies, and checks the export with NanoDa.
Objects, exports and logs stay in external build storage; a receipt is
written to verification/almanac/.
"""
from pathlib import Path
import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
import build
import build_guard as guard
import nanoda

REPO = build.ROOT.parent
ENTRY = "AlmanacSolution"
TARGETS = ["AlmanacSubmission.asymptotic_upper_four", "AlmanacSubmission.explicit_error"]
AXIOMS = nanoda.AXIOMS
LIMIT = 120


def closure(packages):
    root_order, released, external, seen = [], [], {}, set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        if (REPO / relative).exists():
            for dependency in build.imports(REPO / relative):
                visit(dependency)
            root_order.append(module)
        elif (build.ROOT / relative).exists():
            for dependency in build.imports(build.ROOT / relative):
                visit(dependency)
            released.append(module)
        else:
            source, obj = build.resolve_shared(module, packages)
            external[module] = obj.exists()
            if source is not None:
                for dependency in build.imports(source):
                    visit(dependency)

    visit(ENTRY)
    return root_order, released, external


def verify_released(objects, released):
    for module in released:
        relative = Path(*module.split("."))
        obj = (objects / relative).with_suffix(".olean")
        stamp = json.loads(obj.with_suffix(".build.json").read_text())
        source = (build.ROOT / relative).with_suffix(".lean")
        if stamp.get("exit_code") != 0 or build.digest(obj) != stamp.get("olean_sha256"):
            raise RuntimeError("No successful unchanged checked object: " + module)
        if stamp.get("source_sha256") != build.digest(source):
            raise RuntimeError("Checked object was built from a different source: " + module)


def export_worker(output):
    command = [str(build.COMPILER.parent / "leanexport"), ENTRY, "--", *TARGETS]
    with Path(output).open("wb") as f:
        result = subprocess.run(command, stdout=f)
    raise SystemExit(result.returncode)


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--export-worker":
        export_worker(sys.argv[2])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--objects-workspace", type=Path, default=None,
                        help="Workspace holding the released checked objects (default: build.py's)")
    args = parser.parse_args()
    workspace = (args.objects_workspace or build.workspace()).resolve()
    if "Dropbox" in workspace.parts:
        raise RuntimeError("Build storage must be outside Dropbox")
    objects = workspace / ".lake/build/lib/lean"
    packages = build.check_pins()
    root_order, released, external = closure(packages)
    missing = [m for m, present in external.items() if not present]
    if missing:
        raise SystemExit("Missing shared dependency objects; no build started")
    attempt = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    receipt_path = build.RECEIPTS / "almanac" / (attempt + ".json")
    with guard.compiler_slot(workspace.parent / "compile.lock", wait_seconds=0):
        guard.require_free_disk(workspace)
        verify_released(objects, released)
        print(f"Released modules verified unchanged: {len(released)}; external imports: {len(external)}", flush=True)
        directory = workspace.parent / "almanac" / attempt
        sources, outputs, logs = directory / "src", directory / "lib", directory / "logs"
        for path in (sources, outputs, logs):
            path.mkdir(parents=True)
        env = os.environ.copy()
        env["PATH"] = str(build.COMPILER.parent) + os.pathsep + env.get("PATH", "")
        env["LEAN_NUM_THREADS"] = "1"
        env["RAYON_NUM_THREADS"] = "1"
        env["LEAN_PATH"] = os.pathsep.join([str(outputs), str(objects)] +
            [str(Path(p["path"]) / ".lake/build/lib/lean") for p in packages])
        version = subprocess.check_output([str(build.COMPILER), "--version"], text=True).strip()
        if "version 4.35.0," not in version:
            raise RuntimeError("Compiler version mismatch: " + version)
        receipt = {"started_at": attempt, "compiler": version, "workspace": str(directory),
                   "released_objects": str(objects), "released_modules_verified": len(released),
                   "external_imports": len(external), "targets": TARGETS,
                   "permitted_axioms": AXIOMS, "modules": []}

        def save():
            build.write_json(receipt_path, receipt)

        def run(command, name, timeout=LIMIT):
            return guard.run_checked(command, cwd=sources, env=env,
                                     log_path=logs / (name + ".log"), timeout_seconds=timeout)

        for module in root_order + ["AlmanacAxioms"]:
            relative = Path(*module.split(".")).with_suffix(".lean")
            staged = sources / relative
            staged.parent.mkdir(parents=True, exist_ok=True)
            if module == "AlmanacAxioms":
                staged.write_text("import AlmanacSolution\n" +
                                  "".join(f"#print axioms {t}\n" for t in TARGETS))
                command = ["/usr/bin/nice", "-n", "10", str(build.COMPILER), "-M4096", "-j1", str(relative)]
            else:
                shutil.copy2(REPO / relative, staged)
                obj = outputs / relative.with_suffix(".olean")
                obj.parent.mkdir(parents=True, exist_ok=True)
                command = ["/usr/bin/nice", "-n", "10", str(build.COMPILER), "-M4096", "-j1",
                           "-o", str(obj), str(relative)]
            result = run(command, module)
            entry = {"module": module, "source_sha256": build.digest(staged), "command": command,
                     "exit_code": result.returncode, "resource_report": result.resource_report,
                     "output": result.stdout[-12000:]}
            if module != "AlmanacAxioms" and result.returncode == 0:
                entry["olean_sha256"] = build.digest(obj)
            receipt["modules"].append(entry)
            save()
            print(f"{module}: {result.returncode}", flush=True)
            if result.stdout.strip():
                print(result.stdout[-12000:], flush=True)
            if result.returncode != 0:
                raise SystemExit(result.returncode)
        axiom_text = receipt["modules"][-1]["output"]
        for target in TARGETS:
            match = re.search(re.escape(f"'{target}' depends on axioms: [") + r"([^\]]*)\]", axiom_text)
            if not match or set(a.strip() for a in match.group(1).split(",")) - set(AXIOMS):
                raise RuntimeError("Unexpected axioms for " + target)

        partial = directory / "proof.ndjson.partial"
        command = ["/usr/bin/nice", "-n", "10", sys.executable, str(Path(__file__).resolve()),
                   "--export-worker", str(partial)]
        print("Exporting the statements and their proof dependencies.", flush=True)
        export = run(command, "export")
        receipt["export"] = {"command": command,
                             "exporter_command": [str(build.COMPILER.parent / "leanexport"), ENTRY, "--", *TARGETS],
                             "exit_code": export.returncode, "resource_report": export.resource_report}
        save()
        if export.returncode != 0:
            print(export.stdout[-10000:])
            raise SystemExit(export.returncode)
        output = directory / "proof.ndjson"
        os.replace(partial, output)
        nanoda.TARGETS = TARGETS
        receipt["export"].update({"path": str(output), "bytes": output.stat().st_size,
                                  "sha256": nanoda.digest(output), **nanoda.inspect_export(output)})
        checker = build.COMPILER.parent / "nanoda_bin"
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
        receipt["nanoda"] = {"checker": str(checker), "checker_sha256": nanoda.digest(checker),
                             "config": config}
        save()
        print("Export complete:", output.stat().st_size, "bytes; running NanoDa.", flush=True)
        command = ["/usr/bin/nice", "-n", "10", str(checker), str(config_path)]
        checked = run(command, "nanoda")
        receipt["nanoda"].update({"command": command, "exit_code": checked.returncode,
                                  "resource_report": checked.resource_report,
                                  "output": checked.stdout})
        receipt["completed_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()
        if checked.returncode == 0:
            text = (directory / "target-statements.txt").read_text()
            (build.RECEIPTS / "almanac" / (attempt + "-statements.txt")).write_text(text)
        print(checked.stdout[-10000:])
        print("NanoDa exit status:", checked.returncode)
        print("Receipt:", receipt_path)
        raise SystemExit(checked.returncode)


if __name__ == "__main__":
    main()

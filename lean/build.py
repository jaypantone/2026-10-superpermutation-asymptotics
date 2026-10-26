#!/usr/bin/env python3
"""Read fixed shared dependencies; stage and check only this project's modules.

Run --inventory without starting Lean. Ordinary checks never invoke Lake,
fetch a cache, or write through the shared packages symlink.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
RECEIPTS = ROOT.parent / "verification"
DEPENDENCY_ID = "20ac19e7ce5ac332cacf1eb97b947fa08d14ba7f4e50cb6b05776da4db6e23b6"
SHARED = Path.home() / "Library/Caches/LeanShared/dependencies" / DEPENDENCY_ID
COMPILER = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
CORE = COMPILER.parent.parent / "lib/lean"
PROJECT_ID = hashlib.sha256(str(ROOT).encode()).hexdigest()[:16]


def workspace():
    path = Path.home() / "Library/Caches/LeanShared/workspaces" / PROJECT_ID / DEPENDENCY_ID
    if "Dropbox" in path.resolve().parts:
        raise RuntimeError("Build storage must be outside Dropbox")
    return path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path):
    # Strip nested block comments before examining the header.
    text = path.read_text()
    while "/-" in text:
        start = text.index("/-")
        depth, pos = 1, start + 2
        while depth and pos < len(text):
            if text[pos:pos+2] == "/-":
                depth += 1
                pos += 2
            elif text[pos:pos+2] == "-/":
                depth -= 1
                pos += 2
            else:
                pos += 1
        text = text[:start] + "\n" + text[pos:]
    result = []
    for line in text.splitlines():
        line = line.split("--", 1)[0].strip()
        match = re.match(r"(?:(?:public|private|meta)\s+)*import\s+(.+)$", line)
        if match:
            result.extend(token for token in match.group(1).split() if token != "all")
        elif line and line not in {"module", "prelude"}:
            break
    return result


def check_pins():
    original = json.loads((SHARED / "lake-manifest.json").read_text())
    local = json.loads((ROOT / "lake-manifest.json").read_text())
    if original["packages"] != local["packages"]:
        raise RuntimeError("Shared and project dependency locks differ")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0":
        raise RuntimeError("Unexpected project toolchain")
    records = []
    for p in local["packages"]:
        path = SHARED / "packages" / p["name"]
        actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if actual != p["rev"]:
            raise RuntimeError(f"Changed dependency revision: {p['name']}")
        subprocess.run(["git", "-C", str(path), "diff", "--quiet", "HEAD", "--"], check=True)
        records.append({"name": p["name"], "revision": actual, "path": str(path)})
    return records


def resolve_shared(module, packages):
    relative = Path(*module.split("."))
    core = (CORE / relative).with_suffix(".olean")
    if core.exists():
        return None, core
    for p in packages:
        base = Path(p["path"])
        source = (base / relative).with_suffix(".lean")
        if source.exists():
            return source, (base / ".lake/build/lib/lean" / relative).with_suffix(".olean")
    raise RuntimeError("Unresolved external import: " + module)


def import_plan(roots, packages):
    local_order, external, active, visited = [], {}, set(), set()

    def visit(module):
        if module in visited:
            return
        if module in active:
            raise RuntimeError("Import cycle: " + module)
        active.add(module)
        source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if source.exists():
            for dependency in imports(source):
                visit(dependency)
            local_order.append(module)
        else:
            source, obj = resolve_shared(module, packages)
            external[module] = {"olean": str(obj), "present": obj.exists()}
            if source is not None:
                for dependency in imports(source):
                    visit(dependency)
        active.remove(module)
        visited.add(module)

    for module in roots:
        visit(module)
    return local_order, external


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*", default=["Precision"])
    parser.add_argument("--inventory", action="store_true")
    args = parser.parse_args()
    modules = args.modules or ["Precision"]
    for module in modules:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*", module):
            raise RuntimeError("Invalid module name")
    packages = check_pins()
    order, external = import_plan(modules, packages)
    missing = [m for m, data in external.items() if not data["present"]]
    record = {"toolchain": "leanprover/lean4:v4.35.0", "compiler": str(COMPILER),
              "workspace": str(workspace()), "packages": packages,
              "local_order": order, "external_modules": len(external),
              "missing_compiled_dependencies": missing, "compilation_performed": False}
    write_json(RECEIPTS / "import-inventory.json", record)
    print(f"Local modules: {len(order)}; external imports: {len(external)}; missing objects: {len(missing)}", flush=True)
    if missing:
        print("\n".join(missing))
        raise SystemExit("Shared cache addition requires coordinated maintenance; no build started")
    if args.inventory:
        return

    import build_guard as guard
    target = workspace()
    with guard.compiler_slot(target.parent / "compile.lock", wait_seconds=0):
        target.mkdir(parents=True, exist_ok=True)
        guard.require_free_disk(target)
        link = target / ".lake/packages"
        link.parent.mkdir(parents=True, exist_ok=True)
        shared_packages = SHARED / "packages"
        if link.is_symlink():
            if link.resolve() != shared_packages.resolve():
                raise RuntimeError("Unexpected packages symlink")
        elif link.exists():
            raise RuntimeError("Refusing to replace packages directory")
        else:
            link.symlink_to(shared_packages, target_is_directory=True)
        for config in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
            shutil.copy2(ROOT / config, target / config)
        objects = target / ".lake/build/lib/lean"
        logs = target / "logs"
        objects.mkdir(parents=True, exist_ok=True)
        logs.mkdir(exist_ok=True)
        env = os.environ.copy()
        env["LEAN_NUM_THREADS"] = "1"
        env["LEAN_PATH"] = os.pathsep.join([str(objects)] +
            [str(Path(p["path"]) / ".lake/build/lib/lean") for p in packages])
        version = subprocess.check_output([str(COMPILER), "--version"], text=True).strip()
        if "version 4.35.0," not in version:
            raise RuntimeError("Compiler version mismatch: " + version)
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        stage_deadline = time.monotonic() + 10800
        compiled = {}
        reused = 0
        for module in order:
            remaining = int(stage_deadline - time.monotonic())
            if remaining < 1:
                raise RuntimeError("Three-hour build stage deadline reached; no further compiler started")
            guard.require_free_disk(target)
            relative = Path(*module.split("."))
            source = ROOT / relative.with_suffix(".lean")
            staged_source = target / relative.with_suffix(".lean")
            staged_source.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, staged_source)
            output = objects / relative.with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            staged_hash = digest(staged_source)
            if digest(source) != staged_hash:
                raise RuntimeError("Source changed during staging; no compiler started")
            fingerprint = {"source_sha256": staged_hash,
                "imports": {m: compiled[m] for m in imports(source) if m in compiled},
                "manifest_sha256": digest(ROOT / "lake-manifest.json"), "version": version}
            stamp = output.with_suffix(".build.json")
            if stamp.exists() and output.exists() and not output.with_suffix(".publishing.json").exists():
                prior = json.loads(stamp.read_text())
                if (all(prior.get(key) == value for key, value in fingerprint.items()) and
                        prior.get("olean_sha256") == digest(output) and prior.get("exit_code") == 0):
                    compiled[module] = prior["olean_sha256"]
                    reused += 1
                    continue
            if reused:
                print(f"Reused {reused} unchanged checked dependency objects", flush=True)
                reused = 0
            attempt = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
            log = logs / (module + "-" + attempt + ".log")
            with guard.staged_outputs(output) as (temporary, publish):
                command = ["/usr/bin/nice", "-n", "10", str(COMPILER), "-M4096", "-j1",
                           "-o", str(temporary), str(relative.with_suffix(".lean"))]
                result = guard.run_checked(command, cwd=target, env=env, log_path=log,
                                           timeout_seconds=min(120, remaining))
                report = {"module": module, "started_at": started, "command": command,
                          "cwd": str(target), "version": version, **fingerprint,
                          "exit_code": result.returncode, "log": str(log),
                          "resource_report": result.resource_report,
                          "compilation_performed": result.resource_report["launched"],
                          "axiom_output": re.findall(r"'[^'\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", result.stdout)}
                if result.returncode == 0:
                    if digest(source) != fingerprint["source_sha256"]:
                        raise RuntimeError("Source changed during compilation; output not published")
                    publish()
                    report["olean_sha256"] = digest(output)
                    write_json(stamp, report)
                    compiled[module] = report["olean_sha256"]
                write_json(RECEIPTS / "modules" / (module + ".json"), report)
                write_json(RECEIPTS / "attempts" / (module + "-" + attempt + ".json"), report)
                print(module + ": " + str(result.returncode), flush=True)
                if result.returncode != 0 and result.stdout.strip():
                    print(result.stdout[-12000:], flush=True)
                elif report["axiom_output"]:
                    print("\n".join(report["axiom_output"]), flush=True)
                if result.returncode != 0:
                    raise SystemExit(result.returncode)
        if reused:
            print(f"Reused {reused} unchanged checked dependency objects", flush=True)
        write_json(RECEIPTS / "last-build.json", {**record, "version": version,
                   "completed_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "compilation_performed": True, "compiled": compiled, "exit_code": 0})


if __name__ == "__main__":
    main()

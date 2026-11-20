"""Rebuild the supplement and report the axiom dependencies of its public theorems."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

allowed = {"propext", "Classical.choice", "Quot.sound"}

def run(output):
    here = Path(__file__).resolve().parent
    modules = json.loads((here / "modules.json").read_text())
    lean = shutil.which("lean")
    if not lean:
        raise SystemExit("Place Lean 4.28.0 on PATH to rebuild.")
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    print(version, flush=True)
    if not re.search(r"\b4\.28\.0\b", version):
        raise RuntimeError("This build is pinned to Lean 4.28.0.")
    with tempfile.TemporaryDirectory() as name:
        work = Path(name)
        env = dict(os.environ, LEAN_PATH=str(work))
        def check(*args):
            result = subprocess.run([lean, "-j1", "-DwarningAsError=true", *args],
                                    cwd=work, env=env, capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)
            return result.stdout
        for module in modules:
            source = module + ".lean"
            shutil.copy2(here / source, work / source)
            check("-o", module + ".olean", source)
            print("Compiled " + module, flush=True)
        audit = "".join(f"import {m}\n" for m in modules)
        targets = [t for names in modules.values() for t in names]
        if len(targets) != len(set(targets)):
            raise ValueError("Duplicate theorem in manifest")
        audit += "\n" + "".join(f"#print axioms {t}\n" for t in targets)
        (work / "Audit.lean").write_text(audit)
        log = check("Audit.lean")
        for target in targets:
            prefix = "'" + re.escape(target) + r"'\s+"
            match = re.search(prefix + r"depends on axioms:\s*\[([^\]]*)\]", log)
            if match:
                deps = {s.strip() for s in match[1].split(",") if s.strip()}
            elif re.search(prefix + "does not depend on any axioms", log):
                deps = set()
            else:
                raise ValueError("Missing report for " + target)
            if deps - allowed:
                raise ValueError(f"{target} uses additional axioms: {deps - allowed}")
        if output is not None:
            output.mkdir(parents=True, exist_ok=True)
            for f in work.iterdir():
                if f.suffix not in {".lean"}:
                    shutil.copy2(f, output / f.name)
            (output / "Audit.lean").write_text(audit)
            (output / "Axioms.txt").write_text(version + "\n\n" + log)
        print(log, end="")
        print(f"Passed for all {len(targets)} public theorems in {len(modules)} modules.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="save .olean files and the raw axiom report")
    run(parser.parse_args().output)

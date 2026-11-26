"""Build a pinned Lake project and replay one export with four proof checkers."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CONFIG = {
    "spectral": (ROOT / "Analytic435", "AnalyticAudit"),
    "existence": (ROOT / "Analytic435", "ExistenceAudit"),
    "unconditional": (ROOT / "WithGRH435", "UnconditionalAudit"),
    "arithmetic": (ROOT, "Audit"),
}
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", choices=CONFIG)
    parser.add_argument("--lake", default="lake", help="Lake executable for the project toolchain")
    parser.add_argument("--checker-bin", type=Path, help="directory containing the Lean 4.36 checkers (default: PATH)")
    parser.add_argument("--con-leche", type=Path, help="use this con-leche executable for a four-checker replay")
    parser.add_argument("--lean-only", action="store_true",
                        help="check the export with Lean's kernel and audit all its axiom declarations")
    args = parser.parse_args()
    project, module = CONFIG[args.project]
    lake = shutil.which(args.lake)
    if not lake:
        parser.error("Lake executable not found")
    lake = os.path.abspath(lake)

    # Keep child process output untouched, including the byte-oriented proof export.
    def run(argv, **kwargs):
        subprocess.run(argv, cwd=project, check=True, **kwargs)

    toolchain = (project / "lean-toolchain").read_text().strip().split(":v")[-1]
    version = subprocess.check_output([lake, "env", "lean", "--version"], cwd=project, text=True)
    if f"version {toolchain}," not in version and f"version {toolchain} " not in version:
        parser.error(f"expected Lean {toolchain} for {args.project}, found {version.strip()}")
    checker_path = str(args.checker_bin.resolve()) if args.checker_bin else None
    binaries = {}
    checker_names = ["leanchecker"] if args.lean_only else ["leanchecker", "lean4lean", "con-leche", "nanoda_bin"]
    for name in checker_names:
        if name == "con-leche" and args.con_leche:
            binary = shutil.which(str(args.con_leche.resolve()))
        else:
            binary = shutil.which(name, path=checker_path)
        if not binary:
            parser.error(f"cannot find {name}. Set --checker-bin to the Lean 4.36 bin directory")
        binaries[name] = os.path.abspath(binary)

    if args.project == "unconditional":
        # The published GRH dependency includes deprecation warnings on its pinned toolchain.
        run([lake, "build", "+Main", "+OriginalStatements", "+SingleScaleCriterion"])
    else:
        run([lake, "--wfail", "build", module])
    targets = (ROOT / "verification" / f"{args.project}-targets.txt").read_text().splitlines()
    build = project / ".lake" / "build"
    export = build / f"{module}.ndjson"
    with tempfile.TemporaryDirectory(dir=build) as scratch:
        candidate = Path(scratch) / export.name
        if args.project == "unconditional":
            run([lake, "env", sys.executable, str(ROOT / "verification/join-grh.py"),
                 str(candidate.resolve()), *targets])
        else:
            with candidate.open("wb") as stream:
                run([lake, "env", "leanexport", module, "--", *targets], stdout=stream)
        if not candidate.stat().st_size:
            raise RuntimeError("empty proof export")
        relative = os.path.relpath(candidate, project)
        run([binaries["leanchecker"], "--from-export", relative])
        if not args.lean_only:
            run([binaries["lean4lean"], "--import", relative])
            con_leche_args = ["--verified", "--jobs=4"] if args.project == "unconditional" else ["--verified"]
            run([binaries["con-leche"], *con_leche_args, relative])
            config = Path(scratch) / "nanoda.json"
            config.write_text(json.dumps({
                "export_file_path": relative, "permitted_axioms": AXIOMS,
                "unpermitted_axiom_hard_error": True, "nat_extension": True,
                "string_extension": True, "num_threads": 4,
            }), encoding="utf-8")
            run([binaries["nanoda_bin"], str(config)])
        run([sys.executable, str(ROOT / "verification" / "check-axioms.py"), relative])
        candidate.replace(export)
    with export.open("rb") as stream:
        print(hashlib.file_digest(stream, "sha256").hexdigest().upper())
    if args.lean_only:
        print("Lean accepted the export and the axiom audit passed.")
    else:
        print("Lean, lean4lean, con-leche and nanoda accepted the same export.")


if __name__ == "__main__":
    main()

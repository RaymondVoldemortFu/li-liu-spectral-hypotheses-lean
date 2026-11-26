"""Elaborate the combined proof with the two upstream libraries in one Lean environment."""
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def main():
    project = Path.cwd()
    output = Path(sys.argv[1]).resolve()
    scratch = output.parent
    env = os.environ.copy()
    imported = [Path(p).resolve() for p in env["LEAN_PATH"].split(os.pathsep) if p]
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [scratch, *imported])
    lean = shutil.which("lean")
    exporter = shutil.which("leanexport")
    if not lean or not exporter:
        raise RuntimeError("Run this verifier through lake env.")

    # Both upstream packages declare a public, global nabla with a different type.
    # Rebuild the finite difference under a fresh name in an isolated search path.
    module = Path("PrimeNumberTheoremAnd/Wiener.lean")
    source = (project / ".lake/packages/goldbach" / module).read_text(encoding="utf-8")
    digest = hashlib.sha256(source.encode("utf-8")).hexdigest()
    if digest != "25dcfed4f18fce6d9f9951c9dd6af09097fdd108429e586a1dd9abbff82d10e7":
        raise RuntimeError("Unexpected Wiener source at the pinned Goldbach revision.")
    fresh = "wienerForwardDifference"
    if fresh in source or not re.search(r"^def nabla\b", source, re.M):
        raise RuntimeError("Wiener's finite-difference declaration could not be identified.")
    # Lean resolves an entire top-level module directory in the first matching
    # search root. Preserve all sibling artifacts, including the private facets.
    compiled = next(p / module.parent for p in imported if (p / module.with_suffix(".olean")).is_file())
    def link_or_copy(src, dst):
        try:
            os.link(src, dst)
        except OSError:
            shutil.copy2(src, dst)
        return dst
    local = scratch / module
    shutil.copytree(compiled, local.parent, copy_function=link_or_copy,
                    ignore=shutil.ignore_patterns("Wiener.*"))
    local.write_text(re.sub(r"\bnabla\b", fresh, source), encoding="utf-8", newline="\n")
    subprocess.run([lean, "-o", str(local.with_suffix(".olean")), str(module)],
                   cwd=scratch, env=env, check=True)
    root = "UnconditionalAudit"
    subprocess.run([lean, "-DwarningAsError=true", "-o", str(scratch / (root + ".olean")),
                    root + ".lean"], cwd=project, env=env, check=True)
    with output.open("wb") as stream:
        subprocess.run([exporter, root, "--", *sys.argv[2:]], cwd=project, env=env,
                       stdout=stream, check=True)


if __name__ == "__main__":
    main()

"""List all axiom records in a canonical lean4export NDJSON file."""
import json
from pathlib import Path
import subprocess
import sys

ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def audit(source):
    # The pinned lean4export writes one compact record per line.
    result = subprocess.run(
        ["rg", "--no-heading", "--no-filename", "--no-line-number", "--text",
         r'^\{"axiom":', str(source)],
        capture_output=True, check=True,
    )
    wanted = {json.loads(line)["axiom"]["name"] for line in result.stdout.splitlines()}
    names = {0: ""}
    with Path(source).open("rb") as stream:
        for line in stream:
            if line.startswith(b'{"in":'):
                record = json.loads(line)
                idx = record["in"]
                node = record.get("str", record.get("num"))
                component = str(node["str"] if "str" in node else node["i"])
                prefix = names[node["pre"]]
                names[idx] = f"{prefix}.{component}" if prefix else component
                if idx == max(wanted):
                    break
    observed = {names[i] for i in wanted}
    print(f"{Path(source).name} axiom declarations: {', '.join(sorted(observed))}")
    if observed != ALLOWED:
        raise ValueError(f"unexpected axiom set {observed!r}")


if __name__ == "__main__":
    for path in sys.argv[1:]:
        audit(path)


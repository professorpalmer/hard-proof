#!/bin/sh
# Hard Proof, experiment 9: run the link test against real Puppetmaster releases.
# Usage: sh history.sh <scratch dir> [tags...]
set -eu
SCRATCH=${1:?scratch dir}; shift
TAGS=${*:-"v1.28.6 v1.29.0 v1.40.0 v1.50.0 v1.51.0"}
HERE=$(cd "$(dirname "$0")" && pwd)
PM=${PM_REPO:-$HOME/Projects/Puppetmaster}
for tag in $TAGS; do
  dir="$SCRATCH/$tag"
  rm -rf "$dir"; mkdir -p "$dir"
  git -C "$PM" archive "$tag" puppetmaster | tar -x -C "$dir"
  python3 "$HERE/conformance_history.py" --pm "$dir" --tag "$tag" --traces 5000 --seed 1 > "$SCRATCH/$tag.json" || true
  python3 - "$SCRATCH/$tag.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
print(r["code"]["commit"], "version", r["code"]["version"], "|", r["verdict"], "| traces", r["traces"],
      "| differ", r["divergent_traces"], "| law problems", r["traces_with_law_problem"])
if r["first_law_problem"]:
    print("    first law problem:", " ".join(r["first_law_problem"]["trace"]), "->", r["first_law_problem"]["problem"])
PY
done

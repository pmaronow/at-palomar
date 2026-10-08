#!/usr/bin/env bash
# Local counterpart of the current PalomarTemplate comparator check.
# https://github.com/PalomarRegistry/PalomarTemplate/blob/main/scripts/verify-comparator.sh
set -euo pipefail
submission_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$submission_root"
for command_name in bwrap lake lean python3; do
  command -v "$command_name" >/dev/null || {
    echo "Missing required command: $command_name" >&2
    exit 1
  }
done
compiler_prefix=$(lean --print-prefix)
for command_name in lake leanexport leanchecker nanoda_bin con-ron; do
  test -x "$compiler_prefix/bin/$command_name" || {
    echo "Required toolchain executable missing: $command_name" >&2
    exit 1
  }
done
runtime_config=$(mktemp)
trap 'rm -f "$runtime_config"' EXIT
python3 - "$runtime_config" "$compiler_prefix" <<'PYCONFIG'
import json
from pathlib import Path
import sys

config = json.loads(Path("comparator.json").read_text())
if "external_kernels" in config:
    raise SystemExit("Submitted comparator.json may not specify external_kernels")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{sys.argv[2]}/bin/nanoda_bin"],
    "con-ron": [f"{sys.argv[2]}/bin/con-ron"],
}
Path(sys.argv[1]).write_text(json.dumps(config, indent=2) + "\n")
PYCONFIG
lake comparator --config "$runtime_config"

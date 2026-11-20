# Source this after entering the assembled Lean source root.
: "${LEAN_BIN:?absolute bin path of verified Lean 4.35.0}" "${PACKAGES:?absolute path to the nine pinned Lake packages and their cache}"
unset LEAN_PATH LEAN_SRC_PATH
export PATH="$LEAN_BIN:$PATH"
export LEAN_NUM_THREADS=2
test "$(sha256sum "$LEAN_BIN/lean" | cut -d' ' -f1)" = bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38
lean --version | grep eb6cafb7290e8bd5f2937522d8d804f58f02bafc
export PACKAGES
python3 - <<'PY'
from pathlib import Path
import json, os, subprocess
for row in json.loads(Path("lake-manifest.json").read_bytes())["packages"]:
    root = Path(os.environ["PACKAGES"]) / row["name"]
    h = subprocess.check_output(["git", "-C", root, "rev-parse", "HEAD"], text=True).strip()
    assert h == row["rev"], (row["name"], h)
    assert not subprocess.check_output(["git", "-C", root, "status", "--porcelain", "--untracked-files=no"]), row["name"]
    print(row["name"], h)
PY

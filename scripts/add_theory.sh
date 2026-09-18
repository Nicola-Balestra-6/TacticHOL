#!/usr/bin/env bash

# Register a new theory in the four hardcoded lists that drive
# build_corpus.sh, so that the corpus can be rebuilt with it.
#
# Usage:
#   ./scripts/add_theory.sh <name>
# where <name>.ml is a theory file already present in the HOL Light
# root directory, next to define.ml. Theorems in the form
# prove(tm, tac) get their proof steps recorded for training; other
# forms still enter the chronological index as premises.
#
# The theory file must open with a needs of the current last theory
# in the chain, like every HOL Light library file: the recording
# sessions are minimal and rely on that line to load the library.
# The script reads the last theory from the loads_chrono chain,
# checks the needs line, and aborts telling you the exact line to
# add if it is missing.
#
# The script edits, in this tree:
#   scripts/recording/run_rewrite_all.sh    THEORIES
#   scripts/recording/run_record_all.sh     THEORIES
#   scripts/dataset/prepare_chrono_data.py  THEORY_ORDER
#   scripts/dataset/build_chrono_exact.sh   loads_chrono chain
# appending the theory at the end of each list, which places it after
# every existing theory in chronological order. Backups of the four
# files go to /tmp/add_theory_backup_<timestamp>/. It does NOT run the
# rebuild: run ./scripts/build_corpus.sh --rebuild afterwards.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
HOL_ROOT="$(cd "$ROOT_DIR/.." && pwd)"

if [ $# -ne 1 ]; then
  echo "usage: $0 <theory-name>" >&2
  exit 1
fi
NAME="$1"

case "$NAME" in
  *[!a-z0-9_]*|"")
    echo "[add_theory] ABORT: name must match [a-z0-9_]+, got: $NAME" >&2
    exit 1;;
esac

if [ ! -f "$HOL_ROOT/$NAME.ml" ]; then
  echo "[add_theory] ABORT: $HOL_ROOT/$NAME.ml not found." >&2
  echo "[add_theory] Write the theory file first, next to define.ml." >&2
  exit 1
fi

# The current last theory is the last loads_chrono line of the chain.
CHAIN="$ROOT_DIR/scripts/dataset/build_chrono_exact.sh"
LAST="$(grep -o 'loads_chrono "[a-z0-9_]*\.ml"' "$CHAIN" | tail -1 | sed 's/loads_chrono "//; s/\.ml"//')"
if [ -z "$LAST" ]; then
  echo "[add_theory] ABORT: no loads_chrono line found in $CHAIN" >&2
  exit 1
fi

if ! grep -q "^needs \"$LAST\.ml\";;" "$HOL_ROOT/$NAME.ml"; then
  echo "[add_theory] ABORT: $NAME.ml does not load its predecessor." >&2
  echo "[add_theory] The chain currently ends at: $LAST" >&2
  echo "[add_theory] Add this line near the top of $HOL_ROOT/$NAME.ml:" >&2
  echo "" >&2
  echo "  needs \"$LAST.ml\";;" >&2
  echo "" >&2
  exit 1
fi

BACKUP="/tmp/add_theory_backup_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$BACKUP"

ROOT_DIR="$ROOT_DIR" NAME="$NAME" BACKUP="$BACKUP" python3 - << 'PY'
import hashlib, os, shutil, sys

root = os.environ["ROOT_DIR"]
name = os.environ["NAME"]
backup = os.environ["BACKUP"]

def read(path):
    with open(path, "rb") as f:
        return f.read().decode("utf-8")

def sha8(text):
    return hashlib.sha1(text.encode("utf-8")).hexdigest()[:8]

def bash_list_insert(text, entry):
    lines = text.split("\n")
    try:
        start = lines.index("THEORIES=(")
    except ValueError:
        sys.exit("ABORT: line 'THEORIES=(' not found")
    if ("  " + entry) in lines[start:]:
        sys.exit("ABORT: '" + entry + "' already listed")
    for i in range(start + 1, len(lines)):
        if lines[i] == ")":
            lines.insert(i, "  " + entry)
            return "\n".join(lines)
    sys.exit("ABORT: closing ')' of THEORIES not found")

def python_list_insert(text, entry):
    lines = text.split("\n")
    try:
        start = lines.index("THEORY_ORDER = [")
    except ValueError:
        sys.exit("ABORT: line 'THEORY_ORDER = [' not found")
    quoted = '"' + entry + '"'
    if any(quoted in l for l in lines[start:]):
        sys.exit("ABORT: '" + entry + "' already listed")
    for i in range(start + 1, len(lines)):
        if lines[i] == "]":
            lines.insert(i, '    ' + quoted + ',')
            return "\n".join(lines)
    sys.exit("ABORT: closing ']' of THEORY_ORDER not found")

def chrono_insert(text, entry):
    marker = 'loads_chrono "' + entry + '.ml";;'
    if marker in text:
        sys.exit("ABORT: '" + entry + "' already listed")
    lines = text.split("\n")
    last = None
    for i, l in enumerate(lines):
        if l.startswith('loads_chrono "'):
            last = i
    if last is None:
        sys.exit("ABORT: no loads_chrono line found")
    lines[last + 1 : last + 1] = [
        "",
        'chrono_current_theory := "' + entry + '";;',
        marker,
    ]
    return "\n".join(lines)

EDITS = [
    ("scripts/recording/run_rewrite_all.sh", bash_list_insert),
    ("scripts/recording/run_record_all.sh", bash_list_insert),
    ("scripts/dataset/prepare_chrono_data.py", python_list_insert),
    ("scripts/dataset/build_chrono_exact.sh", chrono_insert),
]

results = []
for rel, edit in EDITS:
    path = os.path.join(root, rel)
    old = read(path)
    results.append((path, old, edit(old, name)))

for path, old, new in results:
    shutil.copy2(path, os.path.join(
        backup, os.path.basename(path) + ".bak_" + sha8(old)))
    with open(path, "w", encoding="utf-8") as f:
        f.write(new)
    print("%s  %s %d %d" % (path, sha8(new),
                            new.count(chr(10)), len(new.encode("utf-8"))))

print("backups in " + backup)
PY

echo ""
echo "[add_theory] '$NAME' registered in the four lists."
echo "[add_theory] Now rebuild the corpus:"
echo "  ./scripts/build_corpus.sh --rebuild"

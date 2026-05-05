#!/usr/bin/env bash
# Installs a released ttc archive: creates a venv next to this script,
# installs the bundled wheels offline, and rewrites the ttc shebang so
# ./ttc works without activating the venv.
#
# Override the interpreter with PYTHON=/path/to/python3 ./install.sh
set -e

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PYTHON="${PYTHON:-python3}"
VENV="$HERE/.venv"

"$PYTHON" -m venv "$VENV"
"$VENV/bin/pip" install --upgrade pip >/dev/null
"$VENV/bin/pip" install --no-index --find-links "$HERE/wheels" \
  -r "$HERE/requirements.txt"

python_bin="$VENV/bin/python3"
tmp="$(mktemp)"
printf '#!%s\n' "$python_bin" > "$tmp"
tail -n +2 "$HERE/ttc" >> "$tmp"
mv "$tmp" "$HERE/ttc"
chmod +x "$HERE/ttc"

echo ""
echo "Installed. Try:"
echo "  $HERE/ttc $HERE/example/box_or_lra.smt2"
if [ "$(uname)" = "Darwin" ]; then
  echo ""
  echo "macOS: bundled binaries are unsigned. If Gatekeeper blocks them, run:"
  echo "  xattr -dr com.apple.quarantine \"$HERE\""
fi

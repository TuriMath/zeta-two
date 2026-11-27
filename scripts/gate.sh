#!/bin/sh
# Run the TuriMath gate locally, exactly as CI does. Uses Mathlib's prebuilt cache; never builds Mathlib.
set -e
cd "$(dirname "$0")/.."
lake exe cache get >/dev/null
exec python3 scripts/gate.py "$@"

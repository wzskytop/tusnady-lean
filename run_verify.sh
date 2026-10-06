#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
exec python3 scripts/verify.py --replay "$@"

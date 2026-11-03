#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if [[ -x .tools/lean-4.24.0-linux/bin/lake ]]; then
  export PATH="$PWD/.tools/lean-4.24.0-linux/bin:$PATH"
fi
lake build
lake env lean Audit.lean

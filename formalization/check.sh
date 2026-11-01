#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if [[ -x .tools/lean-4.24.0-linux/bin/lake ]]; then
  export PATH="$PWD/.tools/lean-4.24.0-linux/bin:$PATH"
fi
lake build
lake env lean DPCut.lean
lake env lean AuditLemma12.lean
lake env lean AuditLemma13.lean
lake env lean AuditLemmas14_15.lean
lake env lean AuditLemma16.lean
lake env lean AuditLemma17.lean
lake env lean AuditLemma18.lean
lake env lean AuditLemma19.lean
lake env lean AuditLemma20.lean
lake env lean AuditLemma21.lean
lake env lean AuditLemma22.lean
lake env lean AuditLemma23.lean
lake env lean AuditTheorem1.lean
lake env lean AuditLSW.lean
lake env lean AuditLinearAlgebra.lean
lake env lean AuditImplementation.lean
lake env lean AuditTheorem38.lean
lake env lean AuditAppendixC.lean
lake env lean AuditEllipsoid.lean
lake env lean AuditAll.lean

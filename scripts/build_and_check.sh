#!/usr/bin/env bash
# Run the no-placeholder check and a full lake build.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

bash scripts/check_no_sorry.sh
lake build
echo "PASS: lake build completed"

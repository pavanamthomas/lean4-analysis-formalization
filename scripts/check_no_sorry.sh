#!/usr/bin/env bash
# Reject incomplete-proof tokens and custom axioms in project Lean sources.
# Searches only repository .lean files and excludes .lake.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

mapfile -t files < <(find . -name '*.lean' -not -path './.lake/*' | sort)
if [[ ${#files[@]} -eq 0 ]]; then
  echo "FAIL: no project Lean files found"
  exit 1
fi

fail=0
if grep -nE '\b(sorry|admit)\b' "${files[@]}"; then
  echo "FAIL: found sorry or admit in project Lean sources"
  fail=1
else
  echo "PASS: no sorry or admit in project Lean sources"
fi

if grep -nE '^[[:space:]]*axiom[[:space:]]' "${files[@]}"; then
  echo "FAIL: found a custom axiom declaration in project Lean sources"
  fail=1
else
  echo "PASS: no custom axiom declarations in project Lean sources"
fi

exit "${fail}"

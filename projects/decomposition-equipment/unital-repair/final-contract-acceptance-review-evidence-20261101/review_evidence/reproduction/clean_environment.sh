#!/usr/bin/env bash
# Locator/environment wrapper only. Does not edit any source or dependency.
set -euo pipefail
if [[ "$#" -eq 0 ]]; then
  echo 'Usage: bash clean_environment.sh COMMAND [ARG ...]' >&2
  exit 2
fi
unset PYTHONOPTIMIZE PYTHONPATH LEAN_PATH
export PYTHONDONTWRITEBYTECODE=1
exec "$@"

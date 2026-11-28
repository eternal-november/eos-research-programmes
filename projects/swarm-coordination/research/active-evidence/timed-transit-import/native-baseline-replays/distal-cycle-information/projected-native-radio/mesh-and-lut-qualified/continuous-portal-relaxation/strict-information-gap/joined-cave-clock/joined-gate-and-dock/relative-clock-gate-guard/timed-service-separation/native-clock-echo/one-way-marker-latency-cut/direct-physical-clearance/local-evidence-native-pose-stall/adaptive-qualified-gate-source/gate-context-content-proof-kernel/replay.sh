#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B profile_checks.py | cmp - PROFILES.json
python3 -B verify.py | cmp - EXPECTED.json

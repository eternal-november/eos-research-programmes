#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 timed_controller.py
python3 check_timing_budget.py
python3 check_physical_envelope.py
python3 check_c_controller.py

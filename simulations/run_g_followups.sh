#!/usr/bin/env bash
# Resume the production G2 or G11 sweep, then regenerate summaries from checkpoints.
set -euo pipefail

cd "$(dirname "$0")"
export MPLCONFIGDIR="${MPLCONFIGDIR:-/tmp/g-followup-matplotlib}"

run_name="${1:?choose g2 or g11}"
status_path="figures/${run_name}_run.status"
printf 'running\n' > "$status_path"
trap 'printf "failed\n" > "$status_path"' EXIT

case "$run_name" in
  g2)
    .venv/bin/python -u larger_n_ramp.py
    .venv/bin/python -u tighter_threshold.py
    ;;
  g11)
    .venv/bin/python -u heterogeneous_ramp.py --run
    .venv/bin/python -u heterogeneous_ramp.py
    ;;
  *)
    printf 'unknown sweep: %s\n' "$run_name" >&2
    exit 2
    ;;
esac

.venv/bin/python -u dynamic_ramp_report.py
.venv/bin/python -u simulation_tex.py
printf 'complete\n' > "$status_path"
trap - EXIT

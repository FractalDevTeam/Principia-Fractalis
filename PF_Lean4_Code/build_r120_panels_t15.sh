#!/bin/bash
# r120 (t = 15 specialization) panel driver.
# Serial per module: each 12-node `decide +kernel` module peaks at ~10 GB RSS.
# Same discipline as build_r120_panels.sh.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
LOG=r120_panels_t15.log
: > $LOG
# subpanel files first, then seg assemblies
for f in PF/Analytic/XiPanelsT15/Seg[0-9][0-9]P[0-9].lean PF/Analytic/XiPanelsT15/Seg[0-9][0-9].lean; do
  T=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
  S=$(date +%s)
  OUT=$(lake build "$T" 2>&1 | grep -E "\.lean:[0-9]+:[0-9]+: error|Build completed|build failed" | tail -2 | tr '\n' ' ')
  echo "[$T] $(( $(date +%s)-S ))s :: $OUT" | tee -a $LOG
done

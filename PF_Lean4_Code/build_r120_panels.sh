#!/bin/bash
# r120 (PF.Analytic.XiOnLineZero) panel driver.
# MUST be run serially: each 12-node `decide +kernel` module peaks at ~10 GB RSS,
# so lake's default -j12 will OOM.  ~150 s per part module, ~2 h total.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
LOG=r120_panels.log
: > $LOG
for f in PF/Analytic/XiPanels/*P[0-9].lean PF/Analytic/XiPanels/Seg[0-9][0-9].lean; do
  T=$(echo "$f" | sed 's|/|.|g; s|\.lean$||')
  S=$(date +%s)
  OUT=$(lake build "$T" 2>&1 | grep -E "\.lean:[0-9]+:[0-9]+: error|Build completed|build failed" | tail -2 | tr '\n' ' ')
  echo "[$T] $(( $(date +%s)-S ))s :: $OUT" | tee -a $LOG
done
lake build PF.Analytic.XiOnLineZero 2>&1 | tee -a $LOG | grep -E "error|depends on axioms" -A3

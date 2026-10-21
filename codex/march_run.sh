#!/bin/bash
# march_run.sh -- walk the D = 1 band of the ladder unattended, one box at a
# time, committing each before starting the next.
#
# Scope is deliberately the D = 1 band ONLY: c from 29/4 up to 10 at r = 1/16,
# which is what the current producer can emit. The D >= 2 bands need the two
# remaining prerequisites (parametric density, and the Tier-B M bound), so the
# runner stops at the band edge and says so rather than pretending to continue.
#
# Stops on ANY failure and never escalates density: march_box.sh treats a
# generate failure as the stop signal, because gen_box.py refuses to emit a
# pilot when the box criterion fails, and a centre unreachable at its ladder
# density is a measurement to report, not a knob to turn.
set -u
REPO="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
LOG=/tmp/march_run.log
cd "$REPO" || exit 1

# D = 1 band: centres 29/4, 59/8, 15/2, ... 10, stepping 1/8, radius 1/16.
# Written as eighths to keep every centre an exact dyadic rational.
RAD=1/16
START=58      # 29/4  = 58/8
END=80        #   10  = 80/8

say() { echo "[$(date +%H:%M:%S)] $*" | tee -a "$LOG"; }

say "march_run: D=1 band, centres $((START))/8 .. $((END))/8 at r=$RAD"

for ((e=START; e<=END; e++)); do
  # reduce e/8 to lowest terms for the producer's tag
  n=$e; d=8
  while (( n % 2 == 0 && d % 2 == 0 )); do n=$((n/2)); d=$((d/2)); done
  if (( d == 1 )); then C="$n"; else C="$n/$d"; fi
  TAG="c$(echo "$C" | tr '/' '_')"

  # idempotent: skip a centre whose pilot is already committed
  if git ls-files --error-unmatch \
       "PF_Lean4_Code/PF/Analytic/PilotBoxes/R1_${TAG}_r1_16_pointwise_UNCONDITIONAL_2026_10_20.lean" \
       >/dev/null 2>&1; then
    say "skip  c=$C (already committed)"
    continue
  fi

  FROM=$(python3 -c "from fractions import Fraction as F; print(float(F('$C')-F('$RAD')))")
  TO=$(python3 -c "from fractions import Fraction as F; print(float(F('$C')+F('$RAD')))")

  say "build c=$C r=$RAD  frontier $FROM -> $TO"
  if ! ./codex/march_box.sh "$C" "$RAD" >> "$LOG" 2>&1; then
    say "STOP: march_box.sh failed at c=$C -- $(cat "/tmp/march_${TAG}_status" 2>/dev/null)"
    say "STOP: measured numbers are in /tmp/march_${TAG}_progress; NOT raising density"
    exit 1
  fi
  say "built c=$C : $(cat "/tmp/march_${TAG}_status")"

  if ! ./codex/commit_box.sh "$C" "$RAD" "-" "$FROM" "$TO" >> "$LOG" 2>&1; then
    say "STOP: commit_box.sh refused at c=$C"
    exit 1
  fi
  say "landed c=$C : $(git log --oneline -1)"
done

say "march_run: D=1 band COMPLETE, frontier 10.0625"
say "next band (D=2, c from 10.125) needs prerequisites (1) parametric density"
say "and (2) the Tier-B M bound -- see codex/DENSITY_LADDER_PRICED_2026-10-20.md"
echo "BAND-COMPLETE" > /tmp/march_run_status

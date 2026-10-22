#!/bin/bash
# march_run_schedule.sh -- drive the march from codex/march_schedule.txt.
#
# Supersedes march_run.sh for the D >= 2 bands. march_run.sh hard-coded the D=1
# band's geometry (centres as eighths, r = 1/16, density 1); past the band edge
# the radius and density both vary per box, so the schedule is the input.
#
# The schedule is a PROPOSAL, never trusted: gen_box.py asserts
# 1.25x * Q*r < Mc_lb at generate time on the proof's own Q scale and REFUSES to
# emit a pilot otherwise. A wrong row therefore stops the march with measured
# numbers instead of producing a box that cannot close.
#
# Pablo 2026-10-21: --extend-midpoint ON, safety 1.25x. Both live in
# march_box.sh, so this runner does not re-specify them -- one writer.
#
# Stops on any real failure and NEVER raises density. Lock contention is not a
# failure: march_box.sh now waits (blocking flock -w, matching the Acer YM
# session's convention), and the LOCKED retry below is belt-and-braces for the
# timeout case.
set -u
REPO="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
SCHED="$REPO/codex/march_schedule.txt"
LOG=/tmp/march_sched.log
ST=/tmp/march_sched_status
cd "$REPO" || exit 1
: > "$ST"

say() { echo "[$(date +%H:%M:%S)] $*" | tee -a "$LOG"; }

[ -r "$SCHED" ] || { say "STOP: no schedule at $SCHED"; exit 1; }
say "march_run_schedule: $(grep -vc '^#' "$SCHED") rows from $(basename "$SCHED")"

grep -v '^#' "$SCHED" | while read -r C RAD DENS _rest; do
  [ -z "${C:-}" ] && continue
  TAG="c$(echo "$C" | tr '/' '_')"

  # Idempotent: skip a centre whose unconditional pilot is already committed,
  # so an interrupted march resumes without rebuilding landed boxes.
  if git ls-files --error-unmatch \
       "PF_Lean4_Code/PF/Analytic/PilotBoxes/R1_${TAG}_r${RAD//\//_}_pointwise_UNCONDITIONAL_2026_10_20.lean" \
       >/dev/null 2>&1; then
    say "skip  c=$C (already committed)"
    continue
  fi

  FROM=$(python3 -c "from fractions import Fraction as F; print(float(F('$C')-F('$RAD')))")
  TO=$(python3 -c "from fractions import Fraction as F; print(float(F('$C')+F('$RAD')))")
  say "build c=$C r=$RAD D=$DENS  frontier $FROM -> $TO"

  tries=0
  while :; do
    if ./codex/march_box.sh "$C" "$RAD" "$DENS" >> "$LOG" 2>&1; then break; fi
    st=$(cat "/tmp/march_${TAG}_status" 2>/dev/null)
    case "$st" in
      LOCKED*)
        tries=$((tries+1))
        if [ "$tries" -ge 240 ]; then
          say "STOP: lock held elsewhere for 2h+ at c=$C"; exit 1
        fi
        [ $((tries % 10)) -eq 1 ] && say "waiting: $st (attempt $tries) at c=$C"
        sleep 30
        ;;
      *)
        say "STOP: march_box.sh failed at c=$C -- $st"
        say "STOP: measured numbers in /tmp/march_${TAG}_progress; NOT raising density"
        exit 1
        ;;
    esac
  done
  say "built c=$C : $(cat "/tmp/march_${TAG}_status")"

  if ! ./codex/commit_box.sh "$C" "$RAD" "-" "$FROM" "$TO" >> "$LOG" 2>&1; then
    say "STOP: commit_box.sh refused at c=$C"; exit 1
  fi
  say "landed c=$C : $(git log --oneline -1)"
done

if [ "$(grep -c '^\[.*\] STOP' "$LOG")" -gt 0 ]; then
  echo "STOPPED" > "$ST"
else
  say "march_run_schedule: SCHEDULE COMPLETE"
  echo "SCHEDULE-COMPLETE" > "$ST"
fi

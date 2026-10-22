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
  # Lock contention is NOT a mathematical failure and must not stop the march.
  # The flock is shared with the YM session (Rio section 1), which is told to
  # take it before every lake build -- and march_box.sh takes it with `flock -n`,
  # so a legitimate concurrent YM build makes march_box.sh exit 1. Treating that
  # as a STOP is what halted the band at c = 39/4 on 2026-10-21 at 17:08:51,
  # 33 s before anything of ours even acquired the lock. Retry contention with
  # backoff; stop only on a real generate/build/axiom failure.
  tries=0
  while :; do
    if ./codex/march_box.sh "$C" "$RAD" >> "$LOG" 2>&1; then break; fi
    st=$(cat "/tmp/march_${TAG}_status" 2>/dev/null)
    case "$st" in
      LOCKED*)
        tries=$((tries+1))
        if [ "$tries" -ge 240 ]; then
          say "STOP: lock held by another build for 2h+ at c=$C -- giving up"
          exit 1
        fi
        [ $((tries % 10)) -eq 1 ] && say "waiting: $st (attempt $tries) at c=$C"
        sleep 30
        ;;
      *)
        say "STOP: march_box.sh failed at c=$C -- $st"
        say "STOP: measured numbers are in /tmp/march_${TAG}_progress; NOT raising density"
        exit 1
        ;;
    esac
  done
  say "built c=$C : $(cat "/tmp/march_${TAG}_status")"

  if ! ./codex/commit_box.sh "$C" "$RAD" "-" "$FROM" "$TO" >> "$LOG" 2>&1; then
    say "STOP: commit_box.sh refused at c=$C"
    exit 1
  fi
  say "landed c=$C : $(git log --oneline -1)"
done

say "march_run: D=1 band COMPLETE, frontier 10.0625"
say "next band (D=2, c from 10.125): prerequisite (1) parametric density is DONE"
say "(ab2a4586, --density D); prerequisite (2) Tier-B M is NOT needed -- mmrrrr"
say "and --extend-midpoint are Tier A throughout (52b73083). The D=2 band waits"
say "on Pablo: --extend-midpoint on/off, and safety 1.25x vs 1.0x."
echo "BAND-COMPLETE" > /tmp/march_run_status

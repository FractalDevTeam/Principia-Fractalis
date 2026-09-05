#!/bin/bash
# queue_swap.sh — hand the Acer queue over to the union-aware driver at the next
# strip closure, which is a natural boundary (no panel in flight at the moment the
# closure line is written; at worst we lose the first seconds of the next panel,
# which lake re-does from oleans).
#
# The currently-running strip_queue.sh cannot be edited in place — bash reads a
# script lazily by byte offset, so overwriting a running script can corrupt it.
# So we wait for a clean boundary and swap the whole driver.
set -u
R="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
P="$R/PF_Lean4_Code"
LEDGER="$R/codex/DISPATCH_RESULTS_2026-08-30.md"
LOG=/tmp/r331b_logs/strip_queue.log
ORDER="105 104 103 102 116 115 114 100 113 112 111 110 109 108 107"

echo "SWAP_ARMED $(date -Is) — waiting for the next 'BOX <K> CLOSED' in the queue log"

while true; do
  if grep -qE "^########## BOX [0-9]+ CLOSED" "$LOG" 2>/dev/null; then
    echo "SWAP: closure detected at $(date -Is)"
    grep -E "^########## BOX [0-9]+ CLOSED" "$LOG" | tail -1
    break
  fi
  if ! systemctl --user is-active --quiet pf-strip-queue; then
    echo "SWAP: pf-strip-queue is no longer active — swapping now anyway $(date -Is)"
    break
  fi
  sleep 20
done

systemctl --user stop pf-strip-queue 2>/dev/null || true
sleep 5

# Remaining boxes = those in ORDER whose bridge capstone is not yet present.
REMAIN=""
for K in $ORDER; do
  B="$P/PF/Analytic/RiemannXiBox${K}Bridge.lean"
  if [ -f "$B" ] && grep -q "theorem top15_box${K}_re_lt_neg_1e4" "$B"; then
    echo "SWAP: box $K already CLOSED — dropping from queue"
  else
    REMAIN="$REMAIN $K"
  fi
done
echo "SWAP: remaining strips:$REMAIN"

if [ -z "$REMAIN" ]; then
  echo "SWAP: nothing left to build"
  exit 0
fi

systemd-run --user --unit=pf-endgame-queue --collect --property=Type=simple \
  --property=StandardOutput=append:/tmp/r331b_logs/endgame_queue.log \
  --property=StandardError=append:/tmp/r331b_logs/endgame_queue.log \
  /bin/bash "$P/scripts/endgame_queue.sh" "$P" "$LEDGER" $REMAIN
echo "SWAP_DONE $(date -Is) — pf-endgame-queue launched (union-aware, HOLDs when full)"

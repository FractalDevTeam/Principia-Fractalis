#!/bin/bash
# post_sync_audit.sh — at the next Acer strip closure, re-verify every box whose
# artifacts were SYNCED IN from the Legion by building its Bridge + BridgeAudit on
# the production tree itself, then relaunch the queue with a deduped strip list.
#
# Why build them here at all: the oleans were produced on another machine. Lake
# will either accept them (traces match -> the audit replays in seconds) or rebuild
# them (hash mismatch -> correct, just slower). Either way the audit that goes in
# the ledger is the one the PRODUCTION tree produced, which is the rule.
#
# Runs at a strip boundary so it never contends with a panel.
set -u
R="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
P="$R/PF_Lean4_Code"
LEDGER="$R/codex/DISPATCH_RESULTS_2026-08-30.md"
LOG=/tmp/r331b_logs/endgame_queue.log
LOGDIR=/tmp/r331b_logs
ORDER="104 103 102 116 115 114 100 113 112 111 110 109 108 107"
SYNCED="$*"          # boxes to re-audit here, e.g. "106"
export PATH="$HOME/.elan/bin:$PATH"

echo "POSTSYNC_ARMED $(date -Is) — re-audit on production tree for: $SYNCED"

# Wait for the current box to close, then for the queue to move on (or time out).
before=$(grep -cE "^########## BOX [0-9]+ CLOSED" "$LOG" 2>/dev/null); before=${before:-0}
while true; do
  now=$(grep -cE "^########## BOX [0-9]+ CLOSED" "$LOG" 2>/dev/null); now=${now:-0}
  [ "$now" -gt "$before" ] && { echo "POSTSYNC: closure seen $(date -Is)"; break; }
  systemctl --user is-active --quiet pf-endgame-queue || {
    echo "POSTSYNC: queue no longer active $(date -Is)"; break; }
  sleep 20
done
sleep 150     # let the closure's own union step finish before we take the slot

systemctl --user stop pf-endgame-queue 2>/dev/null || true
sleep 5

cd "$P" || { echo "POSTSYNC_FATAL bad root"; exit 2; }
for K in $SYNCED; do
  echo "########## PRODUCTION AUDIT box $K $(date -Is) ##########"
  rc=0
  for t in "PF.Analytic.RiemannXiBox${K}Bridge" "PF.Analytic.RiemannXiBox${K}BridgeAudit"; do
    /usr/bin/time -f "TIMING $t %e s maxRSS %M kB" nice -n 5 lake build "$t" \
      > "$LOGDIR/prodaudit_${K}.log" 2>&1
    rc=$?
    tail -3 "$LOGDIR/prodaudit_${K}.log" | grep -E '^TIMING' || true
    echo "RC $t = $rc"
    [ "$rc" -ne 0 ] && break
  done
  if [ "$rc" -ne 0 ]; then
    echo "!!! PRODUCTION AUDIT FAILED box $K"
    grep -E 'error:' -A14 "$LOGDIR/prodaudit_${K}.log" | head -40
    echo "| box $K | SYNCED FROM LEGION — production re-audit FAILED | | $(hostname) | $(date -Is) |" >> "$LEDGER"
    continue
  fi
  AXLOG="$LOGDIR/prodaudit_${K}.log"
  AX=$(grep -c "RiemannXiBox${K}BridgeAudit.lean.*depends on axioms" "$AXLOG" 2>/dev/null); AX=${AX:-0}
  RAW=$(grep -A2 "RiemannXiBox${K}BridgeAudit.lean.*depends on axioms" "$AXLOG" 2>/dev/null | tr '\n' ' ')
  BAD=""
  echo "$RAW" | grep -q "sorryAx" && BAD="sorryAx"
  echo "$RAW" | grep -q "ofReduceBool" && BAD="$BAD ofReduceBool"
  echo "PRODUCTION AXIOM AUDIT box $K: $AX checks${BAD:+ — NON-CLEAN: $BAD}"
  HEAD=$(grep -E "^  xi bound" "$LOGDIR/bridge_gen_${K}.log" 2>/dev/null | head -1)
  echo "| box $K | **CLOSED** (built on Legion, re-audited on production tree) ${HEAD} | audit $AX${BAD:+ NON-CLEAN $BAD} | $(hostname) | $(date -Is) |" >> "$LEDGER"
done

# Relaunch with a deduped list: drop every box that already has a capstone.
REMAIN=""
for K in $ORDER; do
  B="$P/PF/Analytic/RiemannXiBox${K}Bridge.lean"
  if [ -f "$B" ] && grep -q "theorem top15_box${K}_re_lt_neg_1e4" "$B"; then
    echo "POSTSYNC: box $K already CLOSED — dropped"
  else
    REMAIN="$REMAIN $K"
  fi
done
echo "POSTSYNC: remaining strips:$REMAIN"
if [ -z "$REMAIN" ]; then echo "POSTSYNC: nothing left"; exit 0; fi

systemd-run --user --unit=pf-endgame-queue --collect --property=Type=simple \
  --property=StandardOutput=append:/tmp/r331b_logs/endgame_queue.log \
  --property=StandardError=append:/tmp/r331b_logs/endgame_queue.log \
  /bin/bash "$P/scripts/endgame_queue.sh" "$P" "$LEDGER" $REMAIN
echo "POSTSYNC_DONE $(date -Is) — queue relaunched"

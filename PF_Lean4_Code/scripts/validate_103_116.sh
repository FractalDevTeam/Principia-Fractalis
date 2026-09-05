set -u
P="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code"
R="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
LOG=/tmp/r331b_logs/endgame_queue.log
export PATH="$HOME/.elan/bin:$PATH"
cd "$P" || exit 2
before=$(grep -cE "^########## BOX [0-9]+ CLOSED" "$LOG" 2>/dev/null); before=${before:-0}
echo "VALIDATE_ARMED $(date -Is) baseline=$before"
while true; do
  now=$(grep -cE "^########## BOX [0-9]+ CLOSED" "$LOG" 2>/dev/null); now=${now:-0}
  [ "$now" -gt "$before" ] && break
  systemctl --user is-active --quiet pf-endgame-queue || break
  sleep 30
done
sleep 150
systemctl --user stop pf-endgame-queue 2>/dev/null || true
sleep 5
echo "VALIDATE: test-building the previously failing target $(date -Is)"
/usr/bin/time -f "TIMING %e s maxRSS %M kB" nice -n 5 lake build PF.Numerics.Box103Seg01M \
  > /tmp/r331b_logs/validate103.log 2>&1
rc=$?
tail -3 /tmp/r331b_logs/validate103.log | grep TIMING || true
echo "RC Box103Seg01M = $rc"
EXTRA=""
if [ "$rc" -eq 0 ]; then
  echo "VALIDATE: integer-literal fix CONFIRMED — requeueing 103 and 116"
  EXTRA="103 116"
  echo "| generator fix | \`N/1\` integer literals defeated \`approx\`; emit_box_segment.py now prints bare integers. Box103Seg01M green. Boxes 103,116 requeued | | $(hostname) | $(date -Is) |" >> "$R/codex/DISPATCH_RESULTS_2026-08-30.md"
else
  echo "VALIDATE: still failing — 103/116 stay parked"
  grep -E "error:" -A8 /tmp/r331b_logs/validate103.log | head -20
  echo "| generator fix | Box103Seg01M STILL FAILING after integer-literal fix — 103,116 remain parked | | $(hostname) | $(date -Is) |" >> "$R/codex/DISPATCH_RESULTS_2026-08-30.md"
fi
ORDER="102 115 114 113 112 111 110 109 108 107 $EXTRA"
REMAIN=""
for K in $ORDER; do
  B="$P/PF/Analytic/RiemannXiBox${K}Bridge.lean"
  if [ -f "$B" ] && grep -q "theorem top15_box${K}_re_lt_neg_1e4" "$B"; then
    echo "VALIDATE: box $K already CLOSED — dropped"
  else
    REMAIN="$REMAIN $K"
  fi
done
echo "VALIDATE: relaunching with:$REMAIN"
[ -z "$REMAIN" ] && exit 0
systemd-run --user --unit=pf-endgame-queue --collect --property=Type=simple \
  --property=StandardOutput=append:/tmp/r331b_logs/endgame_queue.log \
  --property=StandardError=append:/tmp/r331b_logs/endgame_queue.log \
  /bin/bash "$P/scripts/endgame_queue.sh" "$P" "$R/codex/DISPATCH_RESULTS_2026-08-30.md" $REMAIN
echo "VALIDATE_DONE $(date -Is)"

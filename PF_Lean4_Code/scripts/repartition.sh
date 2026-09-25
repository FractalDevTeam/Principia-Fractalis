set -u
P="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code"
R="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
LOG=/tmp/r331b_logs/endgame_queue.log
before=$(grep -cE "^########## BOX [0-9]+ CLOSED" "$LOG"); before=${before:-0}
echo "REPART_ARMED $(date -Is) baseline=$before — Acer will take 113 112 103 116 (Legion owns 107-111)"
while true; do
  now=$(grep -cE "^########## BOX [0-9]+ CLOSED" "$LOG"); now=${now:-0}
  [ "$now" -gt "$before" ] && break
  systemctl --user is-active --quiet pf-endgame-queue || break
  sleep 30
done
sleep 150
systemctl --user stop pf-endgame-queue 2>/dev/null || true
sleep 5
REMAIN=""
for K in 113 112 103 116; do
  B="$P/PF/Analytic/RiemannXiBox${K}Bridge.lean"
  if [ -f "$B" ] && grep -q "theorem top15_box${K}_re_lt_neg_1e4" "$B"; then
    echo "REPART: box $K already CLOSED — dropped"
  else REMAIN="$REMAIN $K"; fi
done
echo "REPART: Acer list:$REMAIN"
[ -z "$REMAIN" ] && exit 0
systemd-run --user --unit=pf-endgame-queue --collect --property=Type=simple \
  --property=StandardOutput=append:/tmp/r331b_logs/endgame_queue.log \
  --property=StandardError=append:/tmp/r331b_logs/endgame_queue.log \
  /bin/bash "$P/scripts/endgame_queue.sh" "$P" "$R/codex/DISPATCH_RESULTS_2026-08-30.md" $REMAIN
echo "REPART_DONE $(date -Is)"

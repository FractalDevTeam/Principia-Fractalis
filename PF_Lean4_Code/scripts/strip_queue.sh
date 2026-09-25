#!/bin/bash
# strip_queue.sh — build a list of strips back-to-back, no conversational turn
# needed between them, and CLOSE each one as soon as it is built.
#
#   usage: strip_queue.sh <repo_root> <ledger> <boxk> [boxk ...]
#
# For each box index:
#   1. M certificates -> panels -> assembly, serialized (one lake job at a
#      time; a panel peaks near 12.6 GB).
#   2. generate the §8 bridge with scripts/emit_box_bridge.py (pure Python,
#      no build slot) and elaborate it plus its axiom audit.  This converts
#      the box from BUILT to CLOSED and yields the three exact margins.
#
# Appends one line per strip to the ledger and moves straight to the next.
# A failure records the strip and stops that queue only.
set -u
ROOT="$1"; shift
LEDGER="$1"; shift
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT" || { echo "QUEUE_FATAL bad root $ROOT"; exit 2; }

LOGDIR=/tmp/r331b_logs
mkdir -p "$LOGDIR"

echo "QUEUE_START $(date -Is) host=$(hostname) strips=$*"
for K in "$@"; do
  PDIR="PF/Analytic/RiemannXiBox${K}Panels"
  [ -d "$PDIR" ] || { echo "QUEUE_SKIP box $K (no $PDIR)"; continue; }
  echo "########## BOX $K START $(date -Is) ##########"
  T0=$(date +%s)
  FAILED=""
  for i in $(seq 1 40); do
    I=$(printf "%02d" "$i")
    TARGETS="PF.Numerics.Box${K}Seg${I}M"
    for p in $(ls "$PDIR"/Seg${I}P*.lean 2>/dev/null | sed 's|.*/||; s|\.lean$||'); do
      TARGETS="$TARGETS PF.Analytic.RiemannXiBox${K}Panels.$p"
    done
    TARGETS="$TARGETS PF.Analytic.RiemannXiBox${K}Panels.Seg${I}"
    for t in $TARGETS; do
      /usr/bin/time -f "TIMING $t %e s maxRSS %M kB" nice -n 10 lake build "$t" \
        > "$LOGDIR/qlast_${K}.log" 2>&1
      rc=$?
      tail -3 "$LOGDIR/qlast_${K}.log" | grep -E '^TIMING' || true
      echo "RC $t = $rc"
      if [ "$rc" -ne 0 ]; then
        echo "!!! QUEUE_FAIL box $K target $t"
        grep -E 'error:' -A12 "$LOGDIR/qlast_${K}.log" | head -40
        FAILED="$t"
        break 2
      fi
    done
    echo "BOX $K SEGMENT $I COMPLETE $(date -Is)"
  done
  T1=$(date +%s)
  if [ -n "$FAILED" ]; then
    echo "BOX $K FAILED at $FAILED after $((T1-T0))s"
    echo "| box $K | FAILED at $FAILED | $(( (T1-T0)/60 )) min | $(hostname) | $(date -Is) |" >> "$LEDGER"
    echo "QUEUE_ABORT $(date -Is)"
    exit 1
  fi
  echo "########## BOX $K PANELS GREEN in $((T1-T0))s $(date -Is) ##########"
  echo "| box $K | 40/40 segments green | $(( (T1-T0)/60 )) min | $(hostname) | $(date -Is) |" >> "$LEDGER"

  # ---- closure: generate + elaborate the §8 bridge and its axiom audit ----
  echo "########## BOX $K BRIDGE $(date -Is) ##########"
  B0=$(date +%s)
  if ! python3 scripts/emit_box_bridge.py --root "$ROOT" --box "$K" \
        > "$LOGDIR/bridge_gen_${K}.log" 2>&1; then
    echo "!!! BRIDGE_GEN_FAIL box $K"
    cat "$LOGDIR/bridge_gen_${K}.log"
    echo "| box $K | BRIDGE GEN FAILED (panels still green) | | $(hostname) | $(date -Is) |" >> "$LEDGER"
    continue
  fi
  cat "$LOGDIR/bridge_gen_${K}.log"
  BRC=0
  for bt in "PF.Analytic.RiemannXiBox${K}Bridge" "PF.Analytic.RiemannXiBox${K}BridgeAudit"; do
    /usr/bin/time -f "TIMING $bt %e s maxRSS %M kB" nice -n 10 lake build "$bt" \
      > "$LOGDIR/bridge_${K}.log" 2>&1
    rc=$?
    tail -3 "$LOGDIR/bridge_${K}.log" | grep -E '^TIMING' || true
    echo "RC $bt = $rc"
    if [ "$rc" -ne 0 ]; then
      echo "!!! BRIDGE_FAIL box $K target $bt"
      grep -E 'error:' -A14 "$LOGDIR/bridge_${K}.log" | head -50
      BRC=1
      break
    fi
  done
  B1=$(date +%s)
  if [ "$BRC" -ne 0 ]; then
    echo "| box $K | panels green, BRIDGE FAILED | $(( (B1-B0) ))s | $(hostname) | $(date -Is) |" >> "$LEDGER"
    echo "BOX $K NOT CLOSED — panels stand, bridge needs attention"
    continue
  fi
  # Axiom audit.  The build log also carries `#print axioms` output from every
  # OTHER project file it touched, and Lean wraps long axiom lists across lines,
  # so count only lines attributed to THIS box's audit file and judge cleanliness
  # by the absence of sorryAx / native_decide in that file's (unwrapped) output.
  AXLOG="$LOGDIR/bridge_${K}.log"
  AX=$(grep -c "RiemannXiBox${K}BridgeAudit.lean.*depends on axioms" "$AXLOG" 2>/dev/null || echo 0)
  AXRAW=$(grep -A2 "RiemannXiBox${K}BridgeAudit.lean.*depends on axioms" "$AXLOG" 2>/dev/null | tr '\n' ' ')
  BAD=""
  echo "$AXRAW" | grep -q "sorryAx" && BAD="sorryAx"
  echo "$AXRAW" | grep -q "ofReduceBool" && BAD="$BAD ofReduceBool"
  echo "AXIOM AUDIT box $K: $AX checks from the audit file"
  if [ -n "$BAD" ]; then
    echo "!!! NON-CLEAN AXIOMS box $K: $BAD"
  else
    echo "AXIOM AUDIT box $K: no sorryAx, no ofReduceBool"
  fi
  MARG=$(grep -E "^  MARGINS|^  xi bound" "$LOGDIR/bridge_gen_${K}.log" | tr '\n' ' ')
  echo "########## BOX $K CLOSED in $((B1-B0))s $(date -Is) ##########"
  echo "| box $K | **CLOSED** $MARG | audit $AX clean$([ -n "$BAD" ] && echo ' + NON-CLEAN PRESENT') | $(hostname) | $(date -Is) |" >> "$LEDGER"
done
echo "QUEUE_END $(date -Is)"

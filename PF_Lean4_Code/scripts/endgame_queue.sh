#!/bin/bash
# endgame_queue.sh — strips -> per-box closure -> incremental top-edge union.
#
#   usage: endgame_queue.sh <repo_root_PF_Lean4_Code> <ledger> <boxk> [boxk ...]
#
# Per box: M certs -> panels -> assembly (serialized, a panel peaks ~12.6 GB), then
# generate + elaborate the §8 bridge and its axiom audit (CLOSED), then regenerate
# and elaborate the top-edge UNION over whatever contiguous prefix is now closed.
#
# The union step is what makes the endgame fire automatically. It runs in the gap
# right after a bridge, so it never contends with a panel. Elaborating it
# incrementally means the case-split scaffold is exercised by the kernel long
# before the last strip lands, instead of all at once at the end.
#
# When the union goes FULL (all 18 boxes closed), this script STOPS and writes a
# HOLD marker. It deliberately does NOT build RiemannXiT15Endgame: Pablo referees
# that step live.
set -u
ROOT="$1"; shift
LEDGER="$1"; shift
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT" || { echo "QUEUE_FATAL bad root $ROOT"; exit 2; }

LOGDIR=/tmp/r331b_logs
mkdir -p "$LOGDIR"
HOLD="$ROOT/../codex/ENDGAME_HOLD.md"

run_union() {
  local K="$1"
  echo "########## UNION after box $K $(date -Is) ##########"
  python3 scripts/emit_top_union.py --root "$ROOT" --partial \
      > "$LOGDIR/union_gen.log" 2>&1
  local grc=$?
  cat "$LOGDIR/union_gen.log"
  if [ "$grc" -ne 0 ]; then
    echo "UNION_GEN_NONFATAL rc=$grc (cover gate or nothing to emit) — continuing"
    return 0
  fi
  local FULL=0
  grep -q "wrote .*RiemannXiTopUnion.lean (FULL" "$LOGDIR/union_gen.log" && FULL=1
  for t in PF.Analytic.RiemannXiTopUnion PF.Analytic.RiemannXiTopUnionAudit; do
    /usr/bin/time -f "TIMING $t %e s maxRSS %M kB" nice -n 5 lake build "$t" \
      > "$LOGDIR/union_${t##*.}.log" 2>&1
    local rc=$?
    tail -3 "$LOGDIR/union_${t##*.}.log" | grep -E '^TIMING' || true
    echo "RC $t = $rc"
    if [ "$rc" -ne 0 ]; then
      echo "!!! UNION_FAIL target $t"
      grep -E 'error:' -A14 "$LOGDIR/union_${t##*.}.log" | head -50
      echo "| union | FAILED after box $K | | $(hostname) | $(date -Is) |" >> "$LEDGER"
      return 1
    fi
  done
  local AXBAD=""
  grep -A2 "RiemannXiTopUnionAudit.lean.*depends on axioms" \
       "$LOGDIR/union_RiemannXiTopUnionAudit.log" 2>/dev/null | tr '\n' ' ' \
       | grep -q "sorryAx" && AXBAD="sorryAx"
  if [ "$FULL" -eq 1 ]; then
    echo "########## UNION FULL — top15_re_lt_neg_1e4 over [1/2,1] $(date -Is) ##########"
    echo "| **UNION FULL** | top15_re_lt_neg_1e4 over [1/2,1] elaborated${AXBAD:+ (AXIOM PROBLEM: $AXBAD)} | | $(hostname) | $(date -Is) |" >> "$LEDGER"
    cat > "$HOLD" <<EOF
# ENDGAME HOLD — $(date -Is)

The top-edge union is FULL and kernel-green:

    PrincipiaTractalis.RiemannXiTopUnion.top15_re_lt_neg_1e4
    PrincipiaTractalis.RiemannXiTopUnion.H_TOP_discharged

Every box in the 18-unit partition of [1/2, 1] is CLOSED.

**STOPPED HERE ON PURPOSE.** The next step consumes this into the boundary chain:

    lake build PF.Analytic.RiemannXiT15Endgame

That module is staged and unbuilt. Pablo referees it live. Do not build it
automatically. NO PUSH.

Axiom check on the union audit: ${AXBAD:-no sorryAx found}
EOF
    echo "HOLD marker written to $HOLD"
    return 2
  fi
  echo "union partial OK${AXBAD:+ (AXIOM PROBLEM: $AXBAD)}"
  return 0
}

echo "QUEUE_START $(date -Is) host=$(hostname) strips=$*"
for K in "$@"; do
  PDIR="PF/Analytic/RiemannXiBox${K}Panels"
  [ -d "$PDIR" ] || { echo "QUEUE_SKIP box $K (no $PDIR)"; continue; }
  echo "########## BOX $K START $(date -Is) ##########"
  T0=$(date +%s); FAILED=""
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
        FAILED="$t"; break 2
      fi
    done
    echo "BOX $K SEGMENT $I COMPLETE $(date -Is)"
  done
  T1=$(date +%s)
  if [ -n "$FAILED" ]; then
    echo "BOX $K FAILED at $FAILED after $((T1-T0))s"
    echo "| box $K | FAILED at $FAILED | $(( (T1-T0)/60 )) min | $(hostname) | $(date -Is) |" >> "$LEDGER"
    echo "QUEUE_ABORT $(date -Is)"; exit 1
  fi
  echo "########## BOX $K PANELS GREEN in $((T1-T0))s $(date -Is) ##########"
  echo "| box $K | 40/40 segments green | $(( (T1-T0)/60 )) min | $(hostname) | $(date -Is) |" >> "$LEDGER"

  # ---- closure ----
  echo "########## BOX $K BRIDGE $(date -Is) ##########"
  B0=$(date +%s)
  if ! python3 scripts/emit_box_bridge.py --root "$ROOT" --box "$K" \
        > "$LOGDIR/bridge_gen_${K}.log" 2>&1; then
    echo "!!! BRIDGE_GEN_FAIL box $K"; cat "$LOGDIR/bridge_gen_${K}.log"
    echo "| box $K | BRIDGE GEN FAILED (panels green) | | $(hostname) | $(date -Is) |" >> "$LEDGER"
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
      BRC=1; break
    fi
  done
  B1=$(date +%s)
  if [ "$BRC" -ne 0 ]; then
    echo "| box $K | panels green, BRIDGE FAILED | $((B1-B0))s | $(hostname) | $(date -Is) |" >> "$LEDGER"
    echo "BOX $K NOT CLOSED — panels stand, bridge needs attention"; continue
  fi
  AXLOG="$LOGDIR/bridge_${K}.log"
  AX=$(grep -c "RiemannXiBox${K}BridgeAudit.lean.*depends on axioms" "$AXLOG" 2>/dev/null || echo 0)
  AXRAW=$(grep -A2 "RiemannXiBox${K}BridgeAudit.lean.*depends on axioms" "$AXLOG" 2>/dev/null | tr '\n' ' ')
  BAD=""
  echo "$AXRAW" | grep -q "sorryAx" && BAD="sorryAx"
  echo "$AXRAW" | grep -q "ofReduceBool" && BAD="$BAD ofReduceBool"
  echo "AXIOM AUDIT box $K: $AX checks${BAD:+ — NON-CLEAN: $BAD}"
  HEAD=$(grep -E "^  xi bound" "$LOGDIR/bridge_gen_${K}.log" | head -1)
  INT=$(grep -E "^  MARGINS" "$LOGDIR/bridge_gen_${K}.log" | head -1)
  echo "########## BOX $K CLOSED in $((B1-B0))s $(date -Is) ##########"
  echo "| box $K | **CLOSED** $HEAD | $INT | audit $AX${BAD:+ NON-CLEAN $BAD} | $(hostname) | $(date -Is) |" >> "$LEDGER"

  # ---- incremental union ----
  run_union "$K"
  urc=$?
  if [ "$urc" -eq 2 ]; then
    echo "QUEUE_HOLD $(date -Is) — union FULL, stopping for live review"
    exit 0
  fi
done
echo "QUEUE_END $(date -Is)"

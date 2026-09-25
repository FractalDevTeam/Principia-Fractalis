#!/bin/bash
# a1_v3.sh — strips -> per-box closure -> bridge.  Successor to a1_v2.sh.
#
#   usage: a1_v3.sh <repo_root_PF_Lean4_Code> <ledger> <boxk> [boxk ...]
#
# ============================================================================
# DRIVER POLICY — STANDING PROHIBITION (added 2026-09-07, a1_v3)
# ============================================================================
#
#   NEVER issue a single `lake build` over a target with a large UNBUILT
#   dependency closure.
#
# This is the third occurrence of one defect family in this campaign. Both
# failure modes are the same mistake and both end in an OOM kill:
#
#   1. SEQUENTIAL ACCUMULATION (Acer, 2026-09-06). c1_rebuild.sh issued one
#      `lake build` per BOX. A single lake process elaborated ~280 modules in
#      sequence and accumulated memory across them until the kernel killed it,
#      reliably near the five-minute mark regardless of the cgroup cap - which
#      is why removing the cap changed nothing. Six OOM kills in 36 minutes.
#
#   2. PARALLEL FAN-OUT (Legion, 2026-09-07). Lake sizes its job pool from
#      `nproc`. The Acer's units are launched by systemd-run with
#      CPUAffinity=0, so nproc=1 there and lake CANNOT fan out - which is why
#      the Acer has never shown this failure. WSL has no systemd, so the
#      Legion's supervisor could not apply that property and its driver ran at
#      nproc=24. When `lake build PF.Analytic.RiemannXiBox108Bridge` hit box 0's
#      unbuilt closure - every Box<K>Bridge imports box 0's bridge for the
#      sigma-universal re/im_join lemmas - lake fanned out into 25 parallel lean
#      processes at ~3.4 GB each. The machine held 13 GB, swapped, and ran at
#      0.0% user CPU for ~25 minutes. Three OOM kills. ZERO completed oleans.
#
#   3. The very first smoke build ran at nproc=4 and fanned out in parallel,
#      which is separately sufficient to explain its OOM.
#
# THE RULE, two parts, both mandatory:
#
#   (a) PIN. Every lake invocation runs under `taskset -c 0`, so nproc=1 and
#       lake's job pool is 1 REGARDLESS of the launcher. This no longer depends
#       on systemd applying CPUAffinity, which is exactly what failed on WSL.
#       There is no `-j`/`--jobs` flag in Lake 5.0.0 - the CPU pin IS the
#       mechanism.
#
#   (b) PREBUILD. Reach every target by building its closure ONE MODULE PER
#       LAKE INVOCATION - each process exits and releases its memory - and only
#       then build the target itself. The pin alone stops the fan-out but not
#       the sequential accumulation in failure mode 1.
#
# `build_one` is the ONLY sanctioned way to invoke lake in this driver. Do not
# add a bare `lake build`.
#
# Corollary: a step that "just builds one target" is not exempt. What matters is
# the size of the UNBUILT closure behind that target, which is invisible at the
# call site. Prebuild it explicitly.
# ============================================================================
#
# Per box: M certs -> panels -> assembly (serialized, a panel peaks ~12.6 GB),
# then generate + elaborate the section-8 bridge and its axiom audit (CLOSED).
#
# The union step is deferred: it needs all 18 boxes and runs after both halves
# merge. This script deliberately does NOT build RiemannXiT15Endgame - Pablo
# referees that step live.
set -u
ROOT="$1"; shift
LEDGER="$1"; shift
export PATH="$HOME/.elan/bin:$PATH"
cd "$ROOT" || { echo "QUEUE_FATAL bad root $ROOT"; exit 2; }

LOGDIR=/tmp/r331b_logs
mkdir -p "$LOGDIR"
HOLD="$ROOT/../codex/ENDGAME_HOLD.md"

# ---------------------------------------------------------------------------
# build_one <target> [logfile]
# The ONLY sanctioned lake invocation. One target, CPU-pinned so lake's job
# pool is 1, own process, exits and releases memory. Returns lake's rc.
# ---------------------------------------------------------------------------
build_one () {
  local t="$1"
  local lf="${2:-$LOGDIR/one_${t//./_}.log}"
  # POLICY (a): taskset -c 0 => nproc=1 => lake job pool = 1. Do not remove.
  # Lake 5.0.0 has no -j/--jobs flag; the CPU pin IS the mechanism.
  /usr/bin/time -f "TIMING $t %e s maxRSS %M kB" \
    taskset -c 0 nice -n 10 lake build "$t" \
    > "$lf" 2>&1
  local rc=$?
  tail -3 "$lf" | grep -E '^TIMING' || true
  echo "RC $t = $rc"
  if [ "$rc" -ne 0 ]; then
    grep -E 'error:' -A14 "$lf" | head -50
  fi
  return $rc
}

# ---------------------------------------------------------------------------
# prebuild_box_closure <K>
# Every module of box K, one lake invocation each. Idempotent: lake skips
# already-built oleans, so this is cheap on a warm tree and is safe to call
# before every bridge.
# ---------------------------------------------------------------------------
prebuild_box_closure () {
  local K="$1"
  local PDIR="PF/Analytic/RiemannXiBox${K}Panels"
  [ -d "$PDIR" ] || { echo "PREBUILD_SKIP box $K (no $PDIR)"; return 0; }
  local i I t p TARGETS
  for i in $(seq 1 40); do
    I=$(printf "%02d" "$i")
    TARGETS="PF.Numerics.Box${K}Seg${I}M"
    for p in $(ls "$PDIR"/Seg${I}P*.lean 2>/dev/null | sed 's|.*/||; s|\.lean$||'); do
      TARGETS="$TARGETS PF.Analytic.RiemannXiBox${K}Panels.$p"
    done
    TARGETS="$TARGETS PF.Analytic.RiemannXiBox${K}Panels.Seg${I}"
    for t in $TARGETS; do
      build_one "$t" "$LOGDIR/qlast_${K}.log" || {
        echo "!!! PREBUILD_FAIL box $K target $t"; return 1; }
    done
  done
  if [ -f "PF/Analytic/RiemannXiBox${K}Envelope.lean" ]; then
    build_one "PF.Analytic.RiemannXiBox${K}Envelope" || {
      echo "!!! PREBUILD_FAIL box $K envelope"; return 1; }
  fi
  return 0
}

# ---------------------------------------------------------------------------
# ensure_box0_reference
# EVERY Box<K>Bridge imports box 0's bridge (the sigma-universal re/im_join
# lemmas, imported with a selective `open`). If box 0's closure is not built,
# building ANY bridge fans out over it - that is the Legion 2026-09-07 incident.
# Build it module-by-module, once, before the first bridge of this run.
#
# Box 0's bridge is HAND-WRITTEN and kernel-green; emit_box_bridge.py refuses it
# by design. Refusal is not failure: we build the committed source as-is.
# ---------------------------------------------------------------------------
BOX0_READY=0
ensure_box0_reference () {
  [ "$BOX0_READY" -eq 1 ] && return 0
  echo "########## BOX0 REFERENCE CLOSURE (prebuild, module-by-module) $(date -Is) ##########"
  prebuild_box_closure 0 || { echo "!!! BOX0_CLOSURE_FAIL"; return 1; }
  local bt
  for bt in PF.Analytic.RiemannXiBox0Bridge PF.Analytic.RiemannXiBox0BridgeAudit; do
    build_one "$bt" "$LOGDIR/bridge_0.log" || { echo "!!! BOX0_REFERENCE_FAIL $bt"; return 1; }
  done
  BOX0_READY=1
  echo "| box 0 | reference closure + hand-written bridge REBUILT from committed source | | $(hostname) | $(date -Is) |" >> "$LEDGER"
  echo "########## BOX0 REFERENCE READY $(date -Is) ##########"
  return 0
}

echo "QUEUE_START $(date -Is) host=$(hostname) driver=a1_v3 strips=$*"

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
      if ! build_one "$t" "$LOGDIR/qlast_${K}.log"; then
        echo "!!! QUEUE_FAIL box $K target $t"
        FAILED="$t"; break 2
      fi
    done
    echo "BOX $K SEGMENT $I COMPLETE $(date -Is)"
  done

  T1=$(date +%s)
  if [ -n "$FAILED" ]; then
    echo "BOX $K FAILED at $FAILED after $((T1-T0))s"
    echo "| box $K | FAILED at $FAILED | $(( (T1-T0)/60 )) min | $(hostname) | $(date -Is) |" >> "$LEDGER"
    echo "C1_ABORT $(date -Is)"; exit 1
  fi
  echo "########## BOX $K PANELS GREEN in $((T1-T0))s $(date -Is) ##########"
  echo "| box $K | 40/40 segments green | $(( (T1-T0)/60 )) min | $(hostname) | $(date -Is) |" >> "$LEDGER"

  # ---- closure ----
  echo "########## BOX $K BRIDGE $(date -Is) ##########"
  B0=$(date +%s)

  # POLICY: the bridge's own import closure must exist before we touch it.
  if ! ensure_box0_reference; then
    echo "| box $K | panels green, BOX0 REFERENCE FAILED | | $(hostname) | $(date -Is) |" >> "$LEDGER"
    echo "BOX $K NOT CLOSED — box 0 reference closure needs attention"; continue
  fi

  # Box 0 is the generator's reference, not a target. Its bridge is already
  # built by ensure_box0_reference above, so box 0 is CLOSED at this point.
  if [ "$K" = "0" ]; then
    B1=$(date +%s)
    echo "########## BOX 0 CLOSED (hand-written reference bridge) in $((B1-B0))s $(date -Is) ##########"
    continue
  fi

  GENRC=0
  python3 scripts/emit_box_bridge.py --root "$ROOT" --box "$K" \
      > "$LOGDIR/bridge_gen_${K}.log" 2>&1 || GENRC=$?
  cat "$LOGDIR/bridge_gen_${K}.log"
  if [ "$GENRC" -ne 0 ]; then
    if grep -qi "^REFUSED" "$LOGDIR/bridge_gen_${K}.log"; then
      # By-design refusal (hand-written reference bridge). NOT a failure.
      echo "BRIDGE_GEN_REFUSED box $K — building the committed bridge as-is"
      echo "| box $K | bridge pre-existing (reference), building committed source | | $(hostname) | $(date -Is) |" >> "$LEDGER"
    else
      echo "!!! BRIDGE_GEN_FAIL box $K"
      echo "| box $K | BRIDGE GEN FAILED (panels green) | | $(hostname) | $(date -Is) |" >> "$LEDGER"
      continue
    fi
  fi

  BRC=0
  for bt in "PF.Analytic.RiemannXiBox${K}Bridge" "PF.Analytic.RiemannXiBox${K}BridgeAudit"; do
    if ! build_one "$bt" "$LOGDIR/bridge_${K}.log"; then
      echo "!!! BRIDGE_FAIL box $K target $bt"; BRC=1; break
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
  echo "$AXRAW" | grep -q "sorryAx"      && BAD="sorryAx"
  echo "$AXRAW" | grep -q "ofReduceBool" && BAD="$BAD ofReduceBool"
  echo "AXIOM AUDIT box $K: $AX checks${BAD:+ — NON-CLEAN: $BAD}"
  HEAD=$(grep -E "^  xi bound" "$LOGDIR/bridge_gen_${K}.log" | head -1)
  INT=$(grep -E "^  MARGINS" "$LOGDIR/bridge_gen_${K}.log" | head -1)
  echo "########## BOX $K CLOSED in $((B1-B0))s $(date -Is) ##########"
  echo "| box $K | **CLOSED** $HEAD | $INT | audit $AX${BAD:+ NON-CLEAN $BAD} | $(hostname) | $(date -Is) |" >> "$LEDGER"
done

echo "C1_BOXES_DONE $(date -Is)"
echo "QUEUE_END $(date -Is)"

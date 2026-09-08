#!/bin/bash
# a1_v4.sh — strips -> per-box closure -> bridge.  Successor to a1_v3.sh.
#
#   usage: a1_v4.sh <repo_root_PF_Lean4_Code> <ledger> <boxk> [boxk ...]
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
# ============================================================================
# v4 CHANGES (2026-09-07)
# ============================================================================
#
#  (a) TOOLCHAIN PREFLIGHT ASSERT. A WSL VM restart on 2026-09-07 left elan's
#      default at a newer stable (4.33.1) while the campaign builds on
#      4.24.0-rc1. The pin held - lean-toolchain overrides the default inside
#      the project - but only because the driver cd's into $ROOT first. If that
#      ever stopped being true, every olean would silently rebuild off-pin,
#      invalidating the tree and breaking gate items C3 and C4 without a single
#      error message. The driver now REFUSES TO START on any mismatch.
#
#  (b) DURABLE PATHS. The same restart cleared /tmp, taking the ledger, the
#      driver log and the pidfile with it. Only a git archive committed earlier
#      that day preserved the box-108 record. Ledger and logs now default under
#      $HOME/pf-rebuild/, which survives a VM restart.
#
#  (c) ARCHIVE AT EVERY CLOSURE, NOT PERIODICALLY. Standing policy after the
#      same incident: the ledger is snapshotted to the archive directory on
#      EVERY closure event, so the durable record can never trail the build by
#      more than one box.
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

# ---------------------------------------------------------------------------
# v4 (a) TOOLCHAIN PREFLIGHT ASSERT — refuse to build off-pin.
# Run AFTER the cd, because that is exactly the condition being asserted:
# elan resolves lean-toolchain relative to the working directory.
# ---------------------------------------------------------------------------
PIN_RAW=$( { tr -d '[:space:]' < "$ROOT/lean-toolchain"; } 2>/dev/null || true)
if [ -z "$PIN_RAW" ]; then
  echo "QUEUE_FATAL no lean-toolchain at $ROOT — refusing to build unpinned"
  exit 3
fi
PIN_VER=${PIN_RAW##*:}; PIN_VER=${PIN_VER#v}
ACT_VER=$(lake --version 2>/dev/null | sed -n 's/.*Lean version \([^,)]*\).*/\1/p')
if [ -z "$ACT_VER" ]; then
  echo "QUEUE_FATAL could not determine the active Lean version"
  exit 3
fi
if [ "$ACT_VER" != "$PIN_VER" ]; then
  echo "QUEUE_FATAL TOOLCHAIN DRIFT: pinned '$PIN_VER' (from $ROOT/lean-toolchain)"
  echo "QUEUE_FATAL                  active '$ACT_VER'"
  echo "QUEUE_FATAL Building off-pin would invalidate every olean and break gate"
  echo "QUEUE_FATAL items C3 (second-machine reproducibility) and C4 (pinned"
  echo "QUEUE_FATAL toolchain) with no error message. Refusing to start."
  exit 3
fi
echo "PREFLIGHT toolchain OK: $ACT_VER matches the pin"

# ---------------------------------------------------------------------------
# v4 (b) DURABLE PATHS — /tmp does not survive a WSL VM restart.
# ---------------------------------------------------------------------------
DURABLE="${PF_DURABLE:-$HOME/pf-rebuild}"
LOGDIR="${PF_LOGDIR:-$DURABLE/r331b_logs}"
ARCHDIR="$DURABLE/ledger_archive"
mkdir -p "$ARCHDIR"
mkdir -p "$LOGDIR"
HOLD="$ROOT/../codex/ENDGAME_HOLD.md"

# ---------------------------------------------------------------------------
# v4 (c) archive_ledger <event>
# Snapshot the ledger to the durable archive on EVERY closure. Standing policy
# after the 2026-09-07 /tmp loss: the durable record must never trail the build
# by more than one box. Cheap - the ledger is a few kB.
# ---------------------------------------------------------------------------
archive_ledger () {
  local ev="${1:-closure}"
  mkdir -p "$ARCHDIR"
  cp -f "$LEDGER" \
     "$ARCHDIR/a1_ledger_$(hostname)_$(date +%Y%m%dT%H%M%S)_${ev}.md" 2>/dev/null || true
  cp -f "$LEDGER" "$ARCHDIR/a1_ledger_$(hostname)_LATEST.md" 2>/dev/null || true
}

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
  archive_ledger "box0-reference"
  echo "########## BOX0 REFERENCE READY $(date -Is) ##########"
  return 0
}

echo "QUEUE_START $(date -Is) host=$(hostname) driver=a1_v4 strips=$*"

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
  archive_ledger "box${K}-panels-green"

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
  archive_ledger "box${K}-closed"
done

echo "C1_BOXES_DONE $(date -Is)"
echo "QUEUE_END $(date -Is)"

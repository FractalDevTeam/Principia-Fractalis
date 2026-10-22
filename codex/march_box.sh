#!/bin/bash
# march_box.sh CENTRE [RADIUS] -- generate, build and verify one box of the
# march to c = 13, serially and lock-guarded.
#
#   ./march_box.sh 57/8          # radius defaults to 1/16
#   ./march_box.sh 165/16 1/32
#
# Writes a one-line verdict to /tmp/march_<tag>_status and a per-module log to
# /tmp/march_<tag>_progress. Peak RSS is ~7 GB of 15 on a single panel module,
# so this NEVER parallelises and refuses to run if another build holds the lock.
set -u
# -M 7000 caps each lean invocation at 7 GB. Measured 2026-10-21: panel modules
# peak at 12.29-12.62 GB UNCAPPED on a 15 GB box -- a 2.7 GB margin against a
# hard OOM while sharing the machine with the YM session. Capped, the same
# modules build fine (Seg01Range_c7 54/54 and Seg01Midpoint_c7 4/4 declarations
# on the three-axiom bar), so that 12 GB is garbage lean declines to collect,
# not live data. Cost: ~16% on range modules, none on midpoint (449 s capped
# vs ~461 s uncapped).
C="${1:?usage: march_box.sh CENTRE [RADIUS] [DENSITY]}"
RAD="${2:-1/16}"
# Density and the midpoint boundary. Pablo 2026-10-21: --extend-midpoint ON and
# safety 1.25x for the whole march. D defaults to 1 so every D=1 invocation --
# including a re-run of any landed box -- stays byte-identical to what landed
# (--extend-midpoint is a no-op at D=1: int(693/1000 * 4) = 2).
DENS="${3:-1}"
EXTRA="--density $DENS --extend-midpoint --safety 1.25"
REPO="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
PROD="$REPO/codex"
# Emergency fallback only; restore explicitly after investigating a repo failure:
# PROD=/tmp/prod
TAG="c$(echo "$C" | tr '/' '_')"
ST="/tmp/march_${TAG}_status"
PG="/tmp/march_${TAG}_progress"

# PER-MODULE locking, not per-box. The lock exists so only one lean runs at a
# time (12 GB peaks on a 15 GB box). Holding it for the whole box is stricter
# than that requires and STARVES the other lane: on 2026-10-21 the Acer YM
# session sat 42 min behind a D=2 box, and at D=32 (193 modules) it would wait
# roughly a day. Acquiring per module keeps the one-lean-at-a-time guarantee
# while letting YM interleave between modules.
LK="flock -w 7200 /tmp/pf_lean_build.lock"
export PATH="$HOME/.elan/bin:$PATH"
: > "$PG"
echo "GENERATING" > "$ST"

# --- 1. generate -----------------------------------------------------------
# The producer refuses to emit a pilot when the box criterion fails, so a
# non-zero exit here means the centre is unreachable at this radius, which is
# the signal to STOP the march rather than raise density silently.
OUT=$(mktemp -d /tmp/march_out.XXXXXX)
if ! (cd "$PROD" && python3 gen_box.py --c "$C" --r "$RAD" $EXTRA --out "$OUT" \
        --work "$(mktemp -d /tmp/march_work.XXXXXX)" > "/tmp/march_${TAG}_gen.log" 2>&1); then
  echo "FAILED generate -- see /tmp/march_${TAG}_gen.log (box criterion?)" > "$ST"
  exit 1
fi
grep -E "geometry|Mc_lb|Q\*r|BOX CRITERION|SAFETY|margin|hybrid (plus|minus)|gate lhs" \
  "/tmp/march_${TAG}_gen.log" >> "$PG"

# --- 2. install into the tree ---------------------------------------------
A="$REPO/PF_Lean4_Code/PF/Analytic"
for f in "$OUT"/*.lean; do
  b=$(basename "$f")
  case "$b" in R1_*) cp "$f" "$A/PilotBoxes/$b" ;; *) cp "$f" "$A/FourierPanels/$b" ;; esac
done
cp "$OUT/_buildorder.txt" "$A/_buildorder.txt"

# --- 3. build, in the producer's own dependency order ---------------------
cd "$REPO/PF_Lean4_Code" || exit 1
FP=".lake/build/lib/lean/PF/Analytic/FourierPanels"
PB=".lake/build/lib/lean/PF/Analytic/PilotBoxes"
mkdir -p "$FP" "$PB"
echo "BUILDING" > "$ST"

while read -r m; do
  [ -z "$m" ] && continue
  $LK taskset -c 0,1 lake env lean -M 7000 -o "$FP/$m.olean" \
    "PF/Analytic/FourierPanels/$m.lean" > "/tmp/march_${TAG}_$m.log" 2>&1
  rc=$?
  echo "$m rc=$rc $(date +%H:%M:%S) freeGB=$(free -g | awk 'NR==2{print $4}')" >> "$PG"
  [ $rc -ne 0 ] && { echo "FAILED $m" > "$ST"; exit 1; }
done < PF/Analytic/_buildorder.txt

GATE=$(cd "$A/PilotBoxes" && ls R1_${TAG}_*_HYBRID_*.lean | head -1)
UNC=$(cd "$A/PilotBoxes" && ls R1_${TAG}_*_UNCONDITIONAL_*.lean | head -1)
$LK taskset -c 0,1 lake env lean -M 7000 -o "$PB/${GATE%.lean}.olean" \
  "PF/Analytic/PilotBoxes/$GATE" > "/tmp/march_${TAG}_gate.log" 2>&1
rc=$?; echo "gate rc=$rc $(date +%H:%M:%S)" >> "$PG"
[ $rc -ne 0 ] && { echo "FAILED gate" > "$ST"; exit 1; }

# Unconditional pilot: no -o, so it is CHECKED, not cached.
$LK taskset -c 0,1 lake env lean -M 7000 "PF/Analytic/PilotBoxes/$UNC" \
  > "/tmp/march_${TAG}_uncond.log" 2>&1
rc=$?; echo "uncond rc=$rc $(date +%H:%M:%S)" >> "$PG"
[ $rc -ne 0 ] && { echo "FAILED uncond" > "$ST"; exit 1; }

# --- 4. exact three-axiom bar on assemble, gate and unconditional logs -----
# Match every generated #print directive to its own output. A clean pilot
# log cannot substitute for missing or contaminated gate/assemble evidence.
for f in "$OUT"/Assemble_*.lean "$OUT/$GATE" "$OUT/$UNC"; do
  b=$(basename "$f" .lean)
  case "$b" in
    Assemble_*) AXLOG="/tmp/march_${TAG}_${b}.log" ;;
    "${GATE%.lean}") AXLOG="/tmp/march_${TAG}_gate.log" ;;
    *) AXLOG="/tmp/march_${TAG}_uncond.log" ;;
  esac
  if ! python3 "$PROD/check_march_axioms.py" "$f" "$AXLOG" >> "$PG" 2>&1; then
    echo "FAILED axiom bar: $AXLOG -- see $PG" > "$ST"; exit 1
  fi
done
echo "DONE c=$C r=$RAD (assemble, gate and unconditional on the exact three-axiom bar)" > "$ST"

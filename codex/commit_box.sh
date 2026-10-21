#!/bin/bash
# commit_box.sh CENTRE RADIUS BOXNUM FRONTIER_FROM FRONTIER_TO
#
# Commits one box of the march to 13, with its measured numbers taken from the
# producer and build logs rather than retyped. REFUSES to commit unless
# march_box.sh recorded DONE and the axiom-bar gate passed -- a box that did not
# pass the bar must not enter the tree.
set -u
C="${1:?usage: commit_box.sh CENTRE RADIUS BOXNUM FRONTIER_FROM FRONTIER_TO}"
RAD="$2"; NUM="$3"; FROM="$4"; TO="$5"
REPO="/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"
TAG="c$(echo "$C" | tr '/' '_')"
ST="/tmp/march_${TAG}_status"
PG="/tmp/march_${TAG}_progress"
U="/tmp/march_${TAG}_uncond.log"

grep -q "^DONE" "$ST" || { echo "REFUSING: $ST is not DONE: $(cat "$ST")"; exit 1; }
grep -q "^axiom-bar OK" "$PG" || { echo "REFUSING: no axiom-bar OK line"; exit 1; }

g() { grep -m1 "$1" "$PG" | sed 's/.*: //; s/^ *//'; }
MCLB=$(grep -m1 "provable Mc_lb" "$PG" | sed 's/.*= //')
LR=$(grep -m1 "L0(" "$PG" | sed 's/.*= //')
RATIO=$(grep -m1 "BOX CRITERION" "$PG" | sed 's/.*(ratio //; s/)//')
MARGIN=$(grep -m1 "margin vs 3/4" "$PG" | sed 's/.*= //; s/ .*//')
REP=$(grep -m1 "hybrid plus" "$PG" | sed 's/.*: //')
IMP=$(grep -m1 "hybrid minus" "$PG" | sed 's/.*: //')
GATE=$(grep -m1 "gate lhs" "$PG" | sed 's/.*= //')
NTH=$(grep -c "depends on axioms" "$U")
HEAD=$(grep -oE "pilot_r1_box_${TAG}_[a-z0-9_]*UNCONDITIONAL" "$U" | head -1)
FIRST=$(grep -m1 "rc=" "$PG" | awk '{print $3}')
LAST=$(grep "uncond rc=" "$PG" | awk '{print $3}')
MODS=$(grep -c "rc=0" "$PG")

MSG=$(mktemp /tmp/cm_box.XXXXXX)
{
printf 'feat(Riemann): box c = %s, r = %s -- march to 13 box %s of 64, kernel-clean, three-axiom bar, frontier %s -> %s\n\n' \
  "$C" "$RAD" "$NUM" "$FROM" "$TO"
printf 'Emitted and built by codex/march_box.sh at the ladder density this band\n'
printf 'prescribes (D = 1, the shipped hybrid: segments 1-2 midpoint, 3-6\n'
printf 'range-brick), and closed on the PARAMETERISED criterion via\n'
printf 'box_of_enclosure_rat -- the local L0, not L = 1; the computed\n'
printf 'Mc_lb, not the fixed 1/8.\n\n'
printf '  centre c        %s\n' "$C"
printf '  radius r        %s\n' "$RAD"
printf '  Re enclosure    %s\n' "$REP"
printf '  Im enclosure    %s\n' "$IMP"
printf '  gate lhs        %s\n' "$GATE"
printf '  Mc_lb           %s\n' "$MCLB"
printf '  L0(c-r)*r       %s\n' "$LR"
printf '  BOX CRITERION   PASS, ratio %s   (parameterised: L0(c-r)*r < Mc_lb)\n' "$RATIO"
printf '  [superseded fixed Mc_lb=1/8 shape: margin %s vs 3/4 -- NOT the\n' "$MARGIN"
printf '   route used; it fails from c = 29/4 on]\n\n'
printf '%s theorems, every one on exactly [propext, Classical.choice, Quot.sound].\n' "$NTH"
printf 'No sorryAx, no nativeDecide, no ofReduceBool; exactly one distinct axiom set\n'
printf 'in the whole #print axioms output, checked as a gate by march_box.sh. The\n'
printf 'unconditional pilot is CHECKED (built without -o), not cached.\n\n'
printf 'Build: %s modules rc=0, %s -> %s serial, taskset -c 0,1, lock-guarded.\n\n' \
  "$MODS" "$FIRST" "$LAST"
printf 'Frontier %s -> %s.\n\n' "$FROM" "$TO"
printf 'Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>\n'
} > "$MSG"

cd "$REPO" || exit 1
git add "PF_Lean4_Code/PF/Analytic/FourierPanels/"*_${TAG}_*.lean \
        "PF_Lean4_Code/PF/Analytic/PilotBoxes/R1_${TAG}_"*.lean || exit 1
git commit -q -F "$MSG" || exit 1
git log --oneline -1

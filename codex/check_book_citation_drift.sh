#!/usr/bin/env bash
# =============================================================================
# check_book_citation_drift.sh — the REVERSE citation gate
#
# The per-chapter Lean gate (2026-11-22) checks book -> Lean: every PF citation
# in the manuscript names a module that actually compiles. This script checks
# the OTHER direction, which had never been checked:
#
#   Lean docstrings cite the manuscript as `chNN:LLL` line references.
#   Do those lines still say what the citing docstring says they say?
#
# They rot silently. Nothing rebuilds when a .tex file gains a paragraph, and
# no grep gate notices, because the citation is a comment. Found 2026-11-24:
# inserting one subsection at ch04:492 on 2026-10-25 shifted the forces
# material +250 lines, so r336's `ch04:493-500` came to point at the subsection
# that RECORDS THE COLLAPSE — the opposite of what its header claims about it.
#
# This script cannot know what a line SHOULD say. It does three things it can
# do mechanically, and leaves judgement to the reader:
#   (1) HARD FAIL  — the cited line is past the end of the chapter file.
#   (2) WARN       — the cited line is blank (a range starting on a blank line
#                    is sloppy but usually harmless; check the range end).
#   (3) REPORT     — print the current content of every cited line so a human
#                    can adjudicate in one pass.
#
# Usage:  ./check_book_citation_drift.sh [/path/to/PF_Lean4_Code] [/path/to/chapters]
#
# NOTE ON THE RESOLVER: a chapter can have MORE THAN ONE .tex file
# (ch20_riemann_hypothesis.tex and ch20_rev2_dirichlet_eta_inserts_*.tex). The
# first draft of this script took `ls chNN_*.tex | head -1`, picked the 238-line
# inserts file over the 817-line chapter, and reported three false OUT OF RANGE
# defects. It now resolves against EVERY candidate and only fails when the line
# is out of range for ALL of them. Do not "simplify" that back.
# =============================================================================
set -uo pipefail

BT="${1:-/home/xluxx/pf-legion-20261120/PF_Lean4_Code}"
BK="${2:-/home/xluxx/pf-push-20261120/Principia_Fractalis_master_folder/chapters}"

[ -d "$BT" ] || { echo "no Lean tree: $BT"; exit 9; }
[ -d "$BK" ] || { echo "no chapters dir: $BK"; exit 9; }
cd "$BT" || exit 9

HARD=0
WARN=0
OK=0

echo "=== Lean -> book citation drift check"
echo "    lean:     $BT"
echo "    chapters: $BK"
echo

TOT=$(grep -rhoE 'ch[0-9]{2}:[0-9]{2,4}' --include='*.lean' PF/ | wc -l)
UNQ=$(grep -rhoE 'ch[0-9]{2}:[0-9]{2,4}' --include='*.lean' PF/ | sort -u | wc -l)
FIL=$(grep -rlE 'ch[0-9]{2}:[0-9]{2,4}' --include='*.lean' PF/ | wc -l)
echo "=== $TOT citations, $UNQ distinct, across $FIL files"
echo

printf '%-11s %-40s %s\n' CITATION 'CITING FILE (first)' 'CURRENT CONTENT OF THAT LINE'
printf '%-11s %-40s %s\n' ---------- '----------------------------------------' '----------------------------'

while IFS=: read -r ch ln; do
  # resolve against EVERY candidate file for this chapter, not just the first
  mapfile -t CANDS < <(ls "$BK"/${ch}_*.tex 2>/dev/null)
  if [ "${#CANDS[@]}" -eq 0 ]; then
    printf '%-11s ** NO CHAPTER FILE FOR %s **\n' "$ch:$ln" "$ch"
    HARD=$((HARD + 1))
    continue
  fi

  BEST=""
  for cf in "${CANDS[@]}"; do
    if [ "$ln" -le "$(wc -l < "$cf")" ]; then BEST="$cf"; break; fi
  done

  WHO=$(grep -rl --include='*.lean' -- "$ch:$ln" PF/ | head -1 | sed 's|^PF/||' | cut -c1-40)

  if [ -z "$BEST" ]; then
    printf '%-11s %-40s ** OUT OF RANGE in all %d candidate file(s) **\n' \
      "$ch:$ln" "$WHO" "${#CANDS[@]}"
    HARD=$((HARD + 1))
    continue
  fi

  TXT=$(sed -n "${ln}p" "$BEST" | sed 's/^[[:space:]]*//' | cut -c1-96)
  if [ -z "$TXT" ]; then
    printf '%-11s %-40s <<BLANK>>  (range start? check the range end)\n' "$ch:$ln" "$WHO"
    WARN=$((WARN + 1))
  else
    printf '%-11s %-40s %s\n' "$ch:$ln" "$WHO" "$TXT"
    OK=$((OK + 1))
  fi
done < <(grep -rhoE 'ch[0-9]{2}:[0-9]{2,4}' --include='*.lean' PF/ | sort -u -t: -k1,1 -k2,2n)

echo
echo "=== resolved $OK   blank $WARN   OUT OF RANGE $HARD"
echo
echo "Line numbers are inherently unstable. Where the manuscript offers a"
echo "\\label{}, cite the LABEL and keep the line number only as a hint:"
echo "  thm:spacetime-emergence   thm:force-emergence   defn:ternary-net"
echo "  def:spectrum-timeless-field   eq:gravity-diff   eq:em-u1"
echo "Theorem NUMBERS are auto-assigned by LaTeX and shift when any earlier"
echo "theorem is inserted, so \"Thm 4.18\" is never a durable reference."

[ "$HARD" -gt 0 ] && exit 1
exit 0

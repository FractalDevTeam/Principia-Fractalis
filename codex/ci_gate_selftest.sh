#!/usr/bin/env bash
# =====================================================================
# ci_gate_selftest.sh — does the axiom gate's verdict logic actually
# reject a bad transcript?
#
# The defect class this guards against is "a check that silently stops
# checking". On 2026-08-10 an orphan sweep imported the AxiomCheck modules
# into PF.lean, which made `lake build PF.AxiomCheck_*` a no-op, which made
# the transcript empty, which made the gate pass. Nothing reported it,
# because a gate that checks nothing reports PASS.
#
# This script feeds known-bad transcripts to BOTH the old verdict logic and
# the proposed replacement, and asserts the old one passes them (the bug)
# while the new one rejects them (the fix).
#
# Usage:
#   ./ci_gate_selftest.sh                # report both, always exit 0
#   ./ci_gate_selftest.sh --expect-fail  # assert NEW logic rejects all bad
#                                        # cases; exit 1 if any slips through
# =====================================================================
set -uo pipefail

MODE="${1:-report}"
TMP="$(mktemp -d)"
trap 'rm -rf "${TMP}"' EXIT

# ---------------------------------------------------------------- fixtures
: > "${TMP}/A_empty.txt"

cat > "${TMP}/B_oneline.txt" <<'EOF'
'PF.headline' depends on axioms: [propext, Classical.choice, myProjectAxiom, Quot.sound]
EOF

cat > "${TMP}/C_wrapped.txt" <<'EOF'
'PF.headline' depends on axioms: [propext,
 Classical.choice,
 myProjectAxiom,
 Quot.sound]
EOF

cat > "${TMP}/D_sorry.txt" <<'EOF'
'PF.broken' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
EOF

# Full-size variants: 4 records, one of which carries a violation. These
# make the AXIOM CHECK the thing that fires, rather than the MIN_RECORDS
# guard -- without them this self-test would pass for the wrong reason.
cat > "${TMP}/B4_oneline.txt" <<'EOF'
'PF.t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.bad' depends on axioms: [propext, Classical.choice, myProjectAxiom, Quot.sound]
EOF

cat > "${TMP}/C4_wrapped.txt" <<'EOF'
'PF.t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.bad' depends on axioms: [propext,
 Classical.choice,
 myProjectAxiom,
 Quot.sound]
EOF

cat > "${TMP}/D4_sorry.txt" <<'EOF'
'PF.t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.broken' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
EOF

cat > "${TMP}/E_good.txt" <<'EOF'
'PF.t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PF.t3' depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.t4' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF

# ------------------------------------------------- OLD logic (verify.sh today)
old_verdict () {
  local out
  out=$(grep -E "depends on axioms:" "$1" \
        | grep -vE "propext|Classical\.choice|Quot\.sound" \
        | grep -v "Hardy1914_published_theorem_substrate_citation" \
        | grep -v "Mayer1991_Cohen2025_substrate_HP_program_citation" \
        | grep -v "Mayer1991_Cohen2025_T3_sym_HP_program_citation" \
        | grep -v "framework_substrate_pins_bulletproof_bundle" \
        || true)
  [[ -z "${out}" ]] && echo PASS || echo FAIL
}

# ------------------------------------------------- NEW logic (proposed patch)
new_verdict () {
  python3 - "$1" 4 <<'PYEOF' >/dev/null 2>&1
import re, sys
log_path, min_records = sys.argv[1], int(sys.argv[2])
text = open(log_path, encoding="utf-8", errors="replace").read()
ALLOWED = {
    "propext", "Classical.choice", "Quot.sound",
    "Hardy1914_published_theorem_substrate_citation",
    "Mayer1991_Cohen2025_substrate_HP_program_citation",
    "Mayer1991_Cohen2025_T3_sym_HP_program_citation",
    "framework_substrate_pins_bulletproof_bundle",
}
REC = re.compile(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)
records = REC.findall(text)
violations = []
for name, body in records:
    axioms = [a.strip() for a in body.split(",") if a.strip()]
    bad = sorted(set(a for a in axioms if a not in ALLOWED))
    if bad:
        violations.append((name, bad))
if len(records) < min_records:
    sys.exit(3)
if violations:
    sys.exit(2)
sys.exit(0)
PYEOF
  local rc=$?
  case "${rc}" in
    0) echo "PASS" ;;
    2) echo "FAIL(axiom)" ;;
    3) echo "FAIL(checked-nothing)" ;;
    *) echo "FAIL(${rc})" ;;
  esac
}

# ---------------------------------------------------------------- run
printf "%-34s %-10s %-24s %s\n" "fixture" "OLD" "NEW" "expected of NEW"
printf "%-34s %-10s %-24s %s\n" "----------------------------------" "----------" \
       "------------------------" "---------------"

declare -i slipped=0

check () {   # $1 = file, $2 = label, $3 = expect ("reject"|"accept")
  local o n
  o=$(old_verdict "$1")
  n=$(new_verdict "$1")
  printf "%-34s %-10s %-24s %s\n" "$2" "${o}" "${n}" "$3"
  if [[ "$3" == "reject" && "${n}" == "PASS" ]]; then slipped+=1; fi
  if [[ "$3" == "accept" && "${n}" != "PASS" ]]; then slipped+=1; fi
}

check "${TMP}/A_empty.txt"   "A empty transcript"            reject
check "${TMP}/B_oneline.txt" "B project axiom, one line"     reject
check "${TMP}/C_wrapped.txt" "C project axiom, wrapped"      reject
check "${TMP}/D_sorry.txt"   "D sorryAx, wrapped"            reject
check "${TMP}/B4_oneline.txt" "B4 violation, 4 recs, 1 line"  reject
check "${TMP}/C4_wrapped.txt" "C4 violation, 4 recs, wrapped" reject
check "${TMP}/D4_sorry.txt"   "D4 sorryAx, 4 recs, wrapped"   reject
check "${TMP}/E_good.txt"    "E clean, 4 records"            accept

echo
echo "OLD logic passes every fixture, including B/C/D which contain real"
echo "violations: 'grep -v' deletes any line mentioning an allowed axiom,"
echo "and every real axiom line mentions propext."
echo
echo "NEW logic parses records structurally (DOTALL, so wrapping is handled),"
echo "checks each axiom name against the allowlist, and treats a transcript"
echo "with too few records as a FAILURE rather than a pass."

if [[ "${MODE}" == "--expect-fail" ]]; then
  if (( slipped > 0 )); then
    echo
    echo "SELFTEST FAILED: ${slipped} fixture(s) got the wrong verdict from NEW logic."
    exit 1
  fi
  echo
  echo "SELFTEST PASSED: new logic rejects all 7 bad fixtures (4 by the record-count\n  guard, 3 by the axiom parser) and accepts the clean one."
fi
exit 0

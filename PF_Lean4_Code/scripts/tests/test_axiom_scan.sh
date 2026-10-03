#!/usr/bin/env bash
# Validate the patched criterion (b) axiom scan against real Lean output.
# Runs OLD and NEW pipelines side by side on each fixture so the difference is
# demonstrated rather than asserted.
set -uo pipefail

LOG="${1:?usage: test_axiom_scan.sh <xavier_confirm.log>}"
TD="$(mktemp -d)"
trap 'rm -rf "$TD"' EXIT

old_scan() {  # the pre-2026-10-02 pipeline
  grep -oE "depends on axioms: \[[^]]*\]" "$1" \
    | tr -d '[]' | sed 's/depends on axioms://' | tr ',' '\n' \
    | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
    | grep -vxF -e propext -e Classical.choice -e Quot.sound || true
}

join_records() {
  awk '
    /depends on axioms:/ {
      acc = $0
      while (acc !~ /\]/) {
        if ((getline nx) <= 0) break
        sub(/^[ \t]*/, "", nx)
        acc = acc " " nx
      }
      print acc
      next
    }
  ' "$1"
}

new_scan() {  # the patched pipeline, including the parse invariant
  local f="$1" j="$TD/j.$$"
  join_records "$f" > "$j"
  local seen joined bad
  seen="$(grep -c 'depends on axioms:' "$f" || true)"
  joined="$(grep -c 'depends on axioms:' "$j" || true)"
  bad="$(sed 's/.*depends on axioms: //' "$j" \
        | tr -d '[]' | tr ',' '\n' \
        | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
        | grep -vxF -e propext -e Classical.choice -e Quot.sound || true)"
  if [ "$joined" -ne "$seen" ]; then
    echo "PARSE_INCOMPLETE joined=$joined seen=$seen"
  elif [ -n "$bad" ]; then
    echo "BAD $(echo "$bad" | tr '\n' ' ')"
  else
    echo "CERTIFY records=$seen"
  fi
}

report() {
  local name="$1" f="$2" expect="$3"
  local o n
  o="$(old_scan "$f" | tr '\n' ' ')"; o="${o:-<empty>}"
  n="$(new_scan "$f")"
  printf '%-34s\n' "$name"
  printf '   matched by OLD regex : %s of %s records\n' \
    "$(grep -oE 'depends on axioms: \[[^]]*\]' "$f" | wc -l)" \
    "$(grep -c 'depends on axioms:' "$f" || true)"
  printf '   OLD verdict          : %s\n' "$([ "$o" = "<empty>" ] && echo 'PASS (no bad axiom seen)' || echo "BAD: $o")"
  printf '   NEW verdict          : %s\n' "$n"
  if [[ "$n" == $expect* ]]; then
    printf '   expected %-20s OK\n\n' "$expect"
  else
    printf '   expected %-20s *** MISMATCH ***\n\n' "$expect"
    FAILED=1
  fi
}

FAILED=0

# T1 -- the real log, untouched
cp "$LOG" "$TD/t1.log"
report "T1 real log, unmodified" "$TD/t1.log" "CERTIFY"

# T2 -- planted non-standard axiom, WRAPPED across lines (the live hazard)
cp "$LOG" "$TD/t2.log"
cat >> "$TD/t2.log" <<'EOF'
info: PF/Fake.lean:1:0: 'PrincipiaTractalis.Fake.planted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PlantedBadAxiom]
EOF
report "T2 planted bad axiom, wrapped" "$TD/t2.log" "BAD"

# T3 -- planted non-standard axiom on a single line (old code caught this one)
cp "$LOG" "$TD/t3.log"
printf "info: PF/Fake.lean:2:0: 'f' depends on axioms: [propext, PlantedBadAxiom]\n" >> "$TD/t3.log"
report "T3 planted bad axiom, one line" "$TD/t3.log" "BAD"

# T4 -- malformed: an unclosed record swallows the next record's opening line
cp "$LOG" "$TD/t4.log"
cat >> "$TD/t4.log" <<'EOF'
info: PF/Fake.lean:3:0: 'a' depends on axioms: [propext,
info: PF/Fake.lean:4:0: 'b' depends on axioms: [propext, Classical.choice, Quot.sound]
EOF
report "T4 malformed, merged records" "$TD/t4.log" "PARSE_INCOMPLETE"

if [ "$FAILED" -eq 0 ]; then echo "ALL FIXTURES BEHAVED AS EXPECTED"; else echo "SOME FIXTURE MISBEHAVED"; fi
exit "$FAILED"

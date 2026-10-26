#!/bin/bash
# NEGATIVE CONTROL on the march axiom gate. Reading the code is not proof it
# can fire -- that is precisely how the CI gate stayed vacuous for 400 runs.
# Feed it doctored source/log pairs and require the right verdict each time.
set -u
cd '/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE' || exit 1
G=codex/check_march_axioms.py
W=/tmp/gatectl; rm -rf "$W"; mkdir -p "$W"

pass=0; fail=0
run() { # run NAME EXPECTED_RC
  local name="$1" want="$2"
  python3 "$G" "$W/$name.lean" "$W/$name.log" >"$W/$name.out" 2>&1
  local rc=$?
  if [ "$rc" = "$want" ]; then
    printf "  PASS  %-28s rc=%s (wanted %s)  %s\n" "$name" "$rc" "$want" "$(head -c 68 "$W/$name.out")"
    pass=$((pass+1))
  else
    printf "  ****  %-28s rc=%s (WANTED %s)  %s\n" "$name" "$rc" "$want" "$(head -c 68 "$W/$name.out")"
    fail=$((fail+1))
  fi
}

# ---- control 0: a well-formed clean pair must be ACCEPTED (rc 0) -----------
printf '#print axioms Foo.bar\n#print axioms Foo.baz\n' > "$W/good.lean"
printf "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Foo.baz' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/good.log"
run good 0

# ---- 1: wrong axiom set (extra axiom) must be REJECTED ---------------------
cp "$W/good.lean" "$W/extra_axiom.lean"
printf "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound, Nonsense.ax]\n'Foo.baz' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/extra_axiom.log"
run extra_axiom 1

# ---- 2: sorryAx anywhere in the log must be REJECTED ----------------------
cp "$W/good.lean" "$W/sorryax.lean"
printf "'Foo.bar' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]\n'Foo.baz' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/sorryax.log"
run sorryax 1

# ---- 3: native_decide residue must be REJECTED ---------------------------
cp "$W/good.lean" "$W/native.lean"
printf "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound, ofReduceBool]\n'Foo.baz' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/native.log"
run native 1

# ---- 4: a MISSING print (log short by one) must be REJECTED ---------------
cp "$W/good.lean" "$W/missing.lean"
printf "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/missing.log"
run missing 1

# ---- 5: WRONG DECLARATION printed must be REJECTED ------------------------
#        the "clean log for the wrong thing" substitution attack
cp "$W/good.lean" "$W/wrongdecl.lean"
printf "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Totally.other' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/wrongdecl.log"
run wrongdecl 1

# ---- 6: too FEW axioms (2 of 3) must be REJECTED -------------------------
cp "$W/good.lean" "$W/short.lean"
printf "'Foo.bar' depends on axioms: [propext, Quot.sound]\n'Foo.baz' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/short.log"
run short 1

# ---- 7: source with NO directives must be REJECTED (empty-gate attack) ----
printf -- '-- no print directives here\n' > "$W/nodir.lean"
cp "$W/good.log" "$W/nodir.log"
run nodir 1

# ---- 8: EXTRA print in the log (contamination) must be REJECTED -----------
cp "$W/good.lean" "$W/extra_print.lean"
printf "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Foo.baz' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Foo.qux' depends on axioms: [propext, Classical.choice, Quot.sound]\n" > "$W/extra_print.log"
run extra_print 1

echo
echo "  negative control: $pass passed, $fail unexpected"
if [ "$fail" -eq 0 ]; then
  echo "  VERDICT: the march axiom gate IS reachable and rejects all 8 attack shapes"
else
  echo "  VERDICT: GATE DEFECT -- $fail case(s) behaved wrongly"
fi
echo DONE

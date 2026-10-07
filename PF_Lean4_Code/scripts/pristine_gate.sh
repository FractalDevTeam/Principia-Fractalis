#!/usr/bin/env bash
# pristine_gate.sh — mechanical "pristine" check for one PF Lean module.
#
# Usage:  scripts/pristine_gate.sh PF.Analytic.SomeModule
#         scripts/pristine_gate.sh PF/Analytic/SomeModule.lean
#
# Exit 0  = PRISTINE (all enforced criteria green)
# Exit 1  = FAILED   (at least one enforced criterion red)
# Exit 2  = usage / environment error
#
# Criteria (per project agreement 2026-09-29):
#   (a) olean CURRENT      — .olean exists and is not older than .lean     [ENFORCED]
#   (b) axioms clean       — #print axioms ⊆ {propext, Classical.choice,
#                            Quot.sound}                                   [ENFORCED]
#   (c) no escape hatches  — no sorry / native_decide / axiom in CODE      [ENFORCED]
#   (d) no dead binders    — no `unused variable` from Lean's own linter   [ENFORCED]
#   (e) non-vacuity        — every `def _ : Prop` has a satisfiability
#                            witness                                        [ENFORCED]
#
# Design note on (d): Lean's `linter.unusedVariables` already detects unused
# binders and emits them as build warnings. The gate parses those rather than
# reimplementing the analysis. `PF/Audit/PremiseAudit.lean` (r337) remains the
# deeper semantic check for dead *hypotheses* that are used syntactically but
# do no proof work; --premise-audit wires it in when available.
#
# Design note on (e): satisfiability is not decidable in general, but a witness
# IS kernel-checkable. The gate therefore requires an authored witness of the
# shape
#       theorem <predname>_nonvacuous : ∃ x, <predname> x := ...
#   or  example : <predname> <args> := ...
# for each Prop-valued definition the module introduces. Absence of a witness is
# an unmet obligation, reported red — not a claim that the predicate is empty.

set -uo pipefail

TREE="${PF_TREE:-/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code}"
ALLOWED_AXIOMS=("propext" "Classical.choice" "Quot.sound")
CPU="${PF_GATE_CPU:-1}"          # keep off core 0 (panel build)
PREMISE_AUDIT=0
QUIET=0

RED=$'\033[31m'; GRN=$'\033[32m'; YEL=$'\033[33m'; RST=$'\033[0m'
[ -t 1 ] || { RED=""; GRN=""; YEL=""; RST=""; }

usage() { sed -n '2,40p' "$0"; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --premise-audit) PREMISE_AUDIT=1; shift ;;
    --semantic-strict) SEMANTIC_STRICT=1; shift ;;
    --quiet|-q)      QUIET=1; shift ;;
    -h|--help)       usage ;;
    -*)              echo "unknown flag: $1" >&2; exit 2 ;;
    *)               TARGET="${1:-}"; shift ;;
  esac
done
[ -n "${TARGET:-}" ] || usage

cd "$TREE" 2>/dev/null || { echo "cannot cd to tree: $TREE" >&2; exit 2; }
export PATH="$HOME/.elan/bin:$PATH"

# --- normalise target to both module name and source path ---------------------
if [[ "$TARGET" == *.lean ]]; then
  SRC="${TARGET#./}"
  MOD="$(printf '%s' "${SRC%.lean}" | tr '/' '.')"
else
  MOD="$TARGET"
  SRC="$(printf '%s' "$MOD" | tr '.' '/').lean"
fi
OLEAN=".lake/build/lib/lean/$(printf '%s' "$MOD" | tr '.' '/').olean"

[ -f "$SRC" ] || { echo "${RED}source not found:${RST} $SRC" >&2; exit 2; }

FAIL=0
declare -a NOTES=()
say() { [ "$QUIET" -eq 1 ] || printf '%s\n' "$*"; }
pass() { say "  ${GRN}PASS${RST}  $1"; }
fail() { say "  ${RED}FAIL${RST}  $1"; FAIL=1; }
warn() { say "  ${YEL}WARN${RST}  $1"; }

say "pristine_gate: $MOD"
say "  source: $SRC"

# --- (a-pre) olean currency BEFORE this run -----------------------------------
# Informational: was the module already kernel-checked when the gate was invoked?
# This is the state a commit claiming "kernel-verified" would have been made in.
if [ ! -f "$OLEAN" ]; then
  PRE_STATE="ABSENT"
elif [ "$SRC" -nt "$OLEAN" ]; then
  PRE_STATE="STALE"
else
  PRE_STATE="CURRENT"
fi
say "  ----  (a-pre) olean before this run: $PRE_STATE"

# --- (c) escape hatches, comments stripped ------------------------------------
# Strip /- ... -/ block comments and -- line comments before scanning, so that
# docstrings saying "no sorry" do not trip the gate (a real false positive we hit).
STRIPPED="$(mktemp)"; trap 'rm -f "$STRIPPED" "$PROBE" "$PROBE_OUT" 2>/dev/null' EXIT
# NOTE: the obvious version of this is WRONG. Truncating `line` to the text
# BEFORE `/-` and then scanning that truncated text for `-/` means a
# single-line `/-- ... -/` docstring opens a block that never closes, and every
# following line gets swallowed until some later `-/`. That silently hides real
# code from criteria (c) and (e) — including a real `sorry`. Accumulate the
# non-comment parts and keep scanning the REMAINDER instead.
awk '
  BEGIN { inblk=0 }
  {
    line=$0; out=""
    while (1) {
      if (inblk) {
        i=index(line,"-/")
        if (i==0) { line=""; break }
        line=substr(line,i+2); inblk=0; continue
      }
      i=index(line,"/-")
      if (i==0) { out=out line; line=""; break }
      out=out substr(line,1,i-1)
      line=substr(line,i+2)
      inblk=1
    }
    sub(/--.*$/,"",out)
    print out
  }' "$SRC" > "$STRIPPED"

HATCH=0
for pat in '\bsorry\b' '\bnative_decide\b' '^[[:space:]]*axiom[[:space:]]'; do
  if grep -qE "$pat" "$STRIPPED"; then
    fail "(c) escape hatch in code: /$pat/"
    grep -nE "$pat" "$STRIPPED" | head -3 | sed 's/^/        /'
    HATCH=1
  fi
done
[ "$HATCH" -eq 0 ] && pass "(c) no sorry / native_decide / axiom in code"

# --- build once, capture output for (b) and (d) -------------------------------
BUILD_OUT="$(mktemp)"; trap 'rm -f "$STRIPPED" "$BUILD_OUT" "$PROBE" "$PROBE_OUT" 2>/dev/null' EXIT
taskset -c "$CPU" nice -n 5 env LEAN_NUM_THREADS=1 \
  lake build "$MOD" > "$BUILD_OUT" 2>&1
BUILD_RC=$?
if [ $BUILD_RC -ne 0 ] || grep -qE '^error:' "$BUILD_OUT"; then
  fail "(build) lake build FAILED — a module that does not compile is never pristine"
  grep -E '^error:' "$BUILD_OUT" | head -5 | sed 's/^/        /'
fi

# --- (a) up-to-date, by LAKE'S OWN CONTENT HASH, not mtime -----------------
# mtime is the WRONG signal. Lake tracks content hashes: a git checkout, stash
# pop or identical rewrite bumps mtime without changing content, and Lake then
# (correctly) refuses to rebuild. Comparing mtimes calls that STALE and produces
# FALSE FAILURES. `lake --no-build` exits nonzero iff the target is not
# up-to-date, which is exactly the question being asked.
if [ ! -f "$OLEAN" ]; then
  fail "(a) olean ABSENT after build — module produced no kernel output"
else
  if taskset -c "$CPU" lake --no-build build "$MOD" >/dev/null 2>&1; then
    pass "(a) UP-TO-DATE per lake content hash (pre-run mtime state: $PRE_STATE)"
  else
    fail "(a) NOT up-to-date per lake --no-build; olean does not cover current source"
  fi
fi

# --- (d) dead binders via Lean's own linter -----------------------------------
# Attribute ONLY warnings whose file path is this module's source. lake build
# output includes the whole dependency chain; attributing a dependency's unused
# binder to the target module is a false accusation, so filter by path.
OWN_UNUSED_ALL="$(grep 'unused variable' "$BUILD_OUT" | grep -F "$SRC:" || true)"
DEP_UNUSED="$(grep 'unused variable' "$BUILD_OUT" | grep -vF "$SRC:" || true)"

# Criteria (d) and (e) can pull in opposite directions. A binder may be
# deliberately unused BECAUSE it closes a vacuous instantiation: strip
# `h_ne : t_lo <= t_hi` from an interval-bound consumer and `t_lo := 1, t_hi := 0`
# makes every hypothesis vacuously provable and the conclusion vacuously true for
# any bound, so a campaign could accumulate green certificates covering zero
# measure. Charging (d) for that guard would reward removing it, which is the
# worse defect. See PF/Analytic/RiemannXiEdgeEnclosure_r331c.lean section
# "Non-degeneracy".
#
# So guard-named binders are exempted from (d) — but ONLY when the module
# actually documents the rationale, and they are always REPORTED, never silently
# dropped. Naming alone must not buy an exemption.
GUARD_RE='unused variable `(h_ne|h_ne[_'"'"'][A-Za-z0-9_'"'"']*|h_nonempty|h_nondegen[A-Za-z0-9_]*)`'
if grep -qiE 'Non-degeneracy|non-vacuity|nondegenerac' "$STRIPPED" 2>/dev/null    || grep -qiE 'Non-degeneracy|non-vacuity|nondegenerac' "$SRC" 2>/dev/null; then
  OWN_GUARDS="$(printf '%s
' "$OWN_UNUSED_ALL" | grep -E "$GUARD_RE" || true)"
  OWN_UNUSED="$(printf '%s
' "$OWN_UNUSED_ALL" | grep -vE "$GUARD_RE" || true)"
else
  OWN_GUARDS=""
  OWN_UNUSED="$OWN_UNUSED_ALL"
fi
if [ -n "$OWN_GUARDS" ]; then
  NG=$(printf '%s
' "$OWN_GUARDS" | grep -c . || true)
  warn "(d*) $NG binder(s) EXEMPTED as documented non-vacuity guards — see the module's rationale"
  printf '%s
' "$OWN_GUARDS" | head -4 | sed 's/^/        /'
fi
if [ -n "$OWN_UNUSED" ]; then
  fail "(d) unused binders in THIS module (linter.unusedVariables)"
  printf '%s
' "$OWN_UNUSED" | head -5 | sed 's/^/        /'
else
  pass "(d) no unused binders in this module"
fi
if [ -n "$DEP_UNUSED" ]; then
  N=$(printf '%s
' "$DEP_UNUSED" | wc -l)
  warn "(d-) $N unused-binder warning(s) in DEPENDENCIES — not charged to this module"
  printf '%s
' "$DEP_UNUSED" | head -3 | sed 's/^/        /'
fi
# --- (d2) semantic dead-hypothesis sweep via PremiseAudit (r337) --------------
# linter.unusedVariables only sees SYNTACTICALLY unused binders. The O-CIRC class
# of defect is semantic: a hypothesis is referenced but its content does no work
# (every field of a premise bundle DEAD, or the hypothesis is definitionally a
# conjunct of the conclusion). r337 detects these; the linter cannot.
mapfile -t AUDIT_DECLS < <(grep -oE '^[[:space:]]*(theorem|lemma)[[:space:]]+[A-Za-z_][A-Za-z0-9_'"'"']*' "$STRIPPED" \
  | awk '{print $2}' | sort -u)
if [ -f "PF/Audit/PremiseAudit.lean" ] && [ "${#AUDIT_DECLS[@]}" -gt 0 ]; then
  AP="$(mktemp --suffix=.lean -p . probe_audit_XXXX)"
  AO="$(mktemp)"
  {
    echo "import $MOD"
    echo "import PF.Audit.PremiseAudit"
    for d in "${AUDIT_DECLS[@]}"; do printf '#audit_all "%s"\n' "$d"; done
  } > "$AP"
  taskset -c "$CPU" nice -n 5 env LEAN_NUM_THREADS=1 \
    lake env lean "$AP" > "$AO" 2>&1
  rm -f "$AP"
  AUDIT_HITS="$(grep -E '^[[:space:]]*(DEAD|CONTAINED|VACUOUS)[[:space:]]' "$AO" || true)"
  if [ -n "$AUDIT_HITS" ]; then
    NH=$(printf '%s\n' "$AUDIT_HITS" | wc -l)
    fail "(d2) PremiseAudit: $NH semantic finding(s) — dead / contained / vacuous premises"
    printf '%s\n' "$AUDIT_HITS" | head -6 | sed 's/^/      /'
    # Show the sweeps that actually CARRY findings. This was `head -3` until
    # 2026-10-05, which on a module with more than three sweeps could display
    # only clean ones while the FAIL line above reported findings -- exactly
    # what happened on PF/SubstrateRigidity.lean, costing a separate
    # full-module #audit_all probe to identify the declaration. The count comes
    # from the untruncated AUDIT_HITS list, so only the display was affected.
    SWEEPHITS="$(grep -E '^O-CIRC SWEEP' "$AO" | grep -v 'withFindings=0' || true)"
    if [ -n "$SWEEPHITS" ]; then
      printf '%s\n' "$SWEEPHITS" | head -8 | sed 's/^/      /'
    else
      grep -E '^O-CIRC SWEEP' "$AO" | head -3 | sed 's/^/      /'
    fi
  else
    pass "(d2) PremiseAudit: no dead / contained / vacuous premises over ${#AUDIT_DECLS[@]} decls"
  fi
  rm -f "$AO"
else
  warn "(d2) PremiseAudit unavailable — semantic premise check SKIPPED"
fi

if [ "$PREMISE_AUDIT" -eq 1 ]; then
  if [ -f "PF/Audit/PremiseAudit.lean" ]; then
    warn "(d+) PremiseAudit hook present; semantic dead-hypothesis sweep not yet wired"
  else
    warn "(d+) PremiseAudit not found"
  fi
fi

# --- (b) axioms, via a generated probe ----------------------------------------
# Do not rely on the module containing its own #print axioms: generate one.
# Probe FULLY-QUALIFIED names. The previous version emitted bare names under a
# single `open` built by pasting every `namespace` line into one dotted path; for
# nested namespaces that names only the innermost scope, so declarations in outer
# namespaces never resolved and produced no axiom record, while the PASS line
# still cited the full declaration count. `sort -u` on bare names also collapsed
# distinct declarations sharing a short name across namespaces. Measured
# 2026-10-02 on PF/GaussLowerBound_r209.lean: 88 bare names -> 3 records;
# 93 qualified names -> 93 records, zero errors.
QUALIFIER="$(dirname "$0")/lib/qualified_decls.py"
if [ ! -f "$QUALIFIER" ]; then
  fail "(b) scripts/lib/qualified_decls.py missing — cannot qualify declaration names"
  DECLS=()
else
  # Run the enumerator to a file and CHECK ITS EXIT STATUS. Reading a process
  # substitution with mapfile discards the status, so a crash mid-output (e.g.
  # UnicodeEncodeError on a cp1252 stdout, Legion 2026-10-03) silently yields
  # a SHORT declaration list that then certifies as a clean pass.
  QOUT="$(mktemp)"; QERR="$(mktemp)"
  if python3 "$QUALIFIER" "$SRC" > "$QOUT" 2> "$QERR"; then
    mapfile -t DECLS < "$QOUT"
  else
    fail "(b) declaration enumeration FAILED — refusing to certify"
    tail -3 "$QERR" | sed 's/^/        /'
    DECLS=()
  fi
  if PRIV_RAW="$(python3 "$QUALIFIER" "$SRC" --private-count 2>/dev/null)"; then
    PRIV="$PRIV_RAW"
  else
    PRIV=0
  fi
  rm -f "$QOUT" "$QERR"
fi
PRIV="${PRIV:-0}"

if [ "${#DECLS[@]}" -eq 0 ]; then
  warn "(b) no theorem/lemma declarations found to probe"
else
  PROBE="$(mktemp --suffix=.lean -p . probe_gate_XXXX)"
  {
    echo "import $MOD"
    for d in "${DECLS[@]}"; do echo "#print axioms $d"; done
  } > "$PROBE"
  PROBE_MOD="$(basename "${PROBE%.lean}")"
  PROBE_OUT="$(mktemp)"
  taskset -c "$CPU" nice -n 5 env LEAN_NUM_THREADS=1 \
    lake env lean "$PROBE" > "$PROBE_OUT" 2>&1
  rm -f "$PROBE"

  if grep -qE "sorryAx" "$PROBE_OUT"; then
    fail "(b) sorryAx present — declaration is not proved"
    grep -B2 'sorryAx' "$PROBE_OUT" | head -6 | sed 's/^/        /'
  fi
  # Lean wraps long axiom lists across lines:
  #     'foo' depends on axioms: [propext,
  #      Classical.choice,
  #      Quot.sound]
  # A per-line regex requiring the closing ']' therefore matches NONE of those
  # records, and the allowlist scan silently skips them. Measured 2026-10-02 on
  # real Lean output: 33 of 195 records matched, 162 skipped, while the PASS line
  # still cited the full declaration count. Join each record onto one line first,
  # and report the number of records actually inspected.
  JOINED="$(mktemp)"
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
  ' "$PROBE_OUT" > "$JOINED"

  # Invariant: every opening record in PROBE_OUT becomes exactly one joined line.
  # A mismatch means the parser lost or merged a record, so nothing is certified.
  REC_SEEN="$(grep -c 'depends on axioms:' "$PROBE_OUT" || true)"
  REC_JOINED="$(grep -c 'depends on axioms:' "$JOINED" || true)"

  # A declaration with NO axiom dependencies prints a different message:
  #     'foo' does not depend on any axioms
  # Counting only 'depends on axioms:' therefore makes an AXIOM-FREE theorem --
  # the strongest possible outcome -- indistinguishable from an unprobed one,
  # and the reconciliation below then WARNs on the best case. Found 2026-10-05
  # on PF/Ch20Ch25NumericObstructions.lean: 3 of 14 declarations are axiom-free
  # (k3_betti_decomposition, k3_gap_is_the_non_pp_part, tier_counts_are_ten_based,
  # all closed by `decide`) and the gate reported "3 produced no axiom record".
  # Counted explicitly below and reconciled alongside REC_SEEN. Conservative:
  # only declarations Lean POSITIVELY reports as axiom-free are reclassified, so
  # a genuinely unprobed declaration -- which prints neither message -- still
  # trips the WARN.
  AXFREE="$(grep -c 'does not depend on any axioms' "$PROBE_OUT" || true)"

  # collect any axiom token that is not on the allowlist
  BAD="$(sed 's/.*depends on axioms: //' "$JOINED" \
        | tr -d '[]' | tr ',' '\n' \
        | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
        | grep -vxF -e propext -e Classical.choice -e Quot.sound || true)"

  if [ "$REC_JOINED" -ne "$REC_SEEN" ]; then
    fail "(b) axiom-record parse incomplete: joined $REC_JOINED of $REC_SEEN records — refusing to certify"
  elif [ -n "$BAD" ]; then
    fail "(b) non-allowlisted axioms:"
    printf '%s\n' "$BAD" | sed 's/^/        /'
    while IFS= read -r tok; do
      [ -n "$tok" ] && grep -F "$tok" "$JOINED" | head -3 | sed 's/^/          /'
    done <<< "$BAD"
  elif ! grep -q 'sorryAx' "$PROBE_OUT"; then
    PRIVNOTE=""
    [ "$PRIV" -gt 0 ] && PRIVNOTE="; $PRIV private declaration(s) not probeable by name — their axioms are covered transitively by the public declarations that use them"
    AXFREENOTE=""
    [ "$AXFREE" -gt 0 ] && AXFREENOTE="; $AXFREE axiom-free (stronger than the allowlist)"
    ACCOUNTED=$(( REC_SEEN + AXFREE ))
    if [ "$ACCOUNTED" -lt "${#DECLS[@]}" ]; then
      warn "(b) axioms ⊆ {propext, Classical.choice, Quot.sound} over $REC_SEEN inspected records$AXFREENOTE, but ${#DECLS[@]} declarations were probed — $(( ${#DECLS[@]} - ACCOUNTED )) produced no axiom record$PRIVNOTE"
    else
      pass "(b) axioms ⊆ {propext, Classical.choice, Quot.sound} over $REC_SEEN inspected axiom records$AXFREENOTE (${#DECLS[@]} probeable declarations$PRIVNOTE)"
    fi
  fi
  rm -f "$JOINED"
fi

# --- (e) non-vacuity obligations ----------------------------------------------
mapfile -t PROPS < <(grep -nE '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+[A-Za-z_][A-Za-z0-9_'"'"']*.*:[[:space:]]*Prop[[:space:]]*:=' "$STRIPPED" \
  | sed -E 's/^[0-9]+:[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+([A-Za-z_][A-Za-z0-9_'"'"']*).*/\2/' | sort -u)

if [ "${#PROPS[@]}" -eq 0 ]; then
  pass "(e) no Prop-valued definitions introduced — no vacuity obligation"
else
  MISSING=()
  for p in "${PROPS[@]}"; do
    # a witness is: an ∃ statement mentioning p, an `example : p ...`, or a
    # theorem whose statement applies p to concrete arguments.
    # FIXED 2026-10-07. The five suffix alternatives previously carried no
    # $p, so ONE theorem named *_holds anywhere in a module satisfied (e)
    # for EVERY Prop in it. That contradicted the design note above, which
    # specifies the witness shape as `<predname>_nonvacuous`. Measured
    # effect of the bug: 167 of the 1019 modules reported PRISTINE by the
    # 2026-10-06 sweep passed (e) on the bare token alone, between them
    # holding 716 Prop definitions with no witness naming them. Each token
    # is now bound to the predicate.
    if grep -qE "(∃[^,]*,[^\n]*\b$p\b|example[[:space:]]*:[[:space:]]*$p\b|\b${p}_(nonvacuous|nonempty|satisfiable|holds|witness)\b)" "$STRIPPED" \
       && grep -qE "\b$p\b" "$STRIPPED"; then
      :
    else
      MISSING+=("$p")
    fi
  done
  if [ "${#MISSING[@]}" -gt 0 ]; then
    fail "(e) Prop definitions without a satisfiability witness:"
    printf '%s\n' "${MISSING[@]}" | sed 's/^/        /'
    say "        expected: theorem <name>_nonvacuous : ∃ x, <name> x := ..."
  else
    pass "(e) all ${#PROPS[@]} Prop definitions carry a satisfiability witness"
  fi
fi

# --- (f) semantic hygiene: conclusions and definition bodies -------------------
# (d2) PremiseAudit policies HYPOTHESES. Nothing before this point looks at what
# a theorem CONCLUDES, so a theorem with live premises and a `Prop := True`
# conclusion passes every other criterion. Criterion (f) closes that gap.
#
# DIAGNOSTIC BY DEFAULT: reported, and only counted toward the verdict when
# --semantic-strict is given. The findings need their intended theorem located,
# not an automatic downgrade.
SHG="scripts/semantic_hygiene_gate.py"
if [ -f "$SHG" ]; then
  SHG_OUT="$(mktemp)"
  if python3 "$SHG" --module "$MOD" > "$SHG_OUT" 2>&1; then
    SHG_RC=0
  else
    SHG_RC=$?
  fi
  SHG_HARD="$(grep -c '  FAIL  (f)' "$SHG_OUT" 2>/dev/null || true)"
  SHG_SOFT="$(grep -c '  WARN  (f)' "$SHG_OUT" 2>/dev/null || true)"
  if [ "$SHG_RC" -eq 2 ]; then
    say "  ----  (f) semantic hygiene: module source not resolvable — skipped"
  elif [ "${SHG_HARD:-0}" -gt 0 ]; then
    if [ "${SEMANTIC_STRICT:-0}" -eq 1 ]; then
      fail "(f) semantic hygiene: $SHG_HARD hard finding(s) in conclusions / definition bodies"
    else
      say "  ${YLW:-}WARN${RST:-}  (f) semantic hygiene: $SHG_HARD hard, ${SHG_SOFT:-0} soft — DIAGNOSTIC, not counted (pass --semantic-strict to enforce)"
    fi
    grep -E '  (FAIL|WARN)  \(f\)' "$SHG_OUT" | head -6 | sed 's/^  /      /'
    grep -E '        REPAIR:' "$SHG_OUT" | head -2 | sed 's/^        /      /'
  elif [ "${SHG_SOFT:-0}" -gt 0 ]; then
    say "  ${YLW:-}WARN${RST:-}  (f) semantic hygiene: ${SHG_SOFT} soft finding(s), no hard findings"
  else
    pass "(f) semantic hygiene: no conclusion-level or definition-body findings"
  fi
  rm -f "$SHG_OUT" 2>/dev/null || true
else
  say "  ----  (f) semantic hygiene: $SHG absent — skipped"
fi

# --- verdict ------------------------------------------------------------------
if [ "$FAIL" -eq 0 ]; then
  say "${GRN}PRISTINE${RST}  $MOD"
  exit 0
else
  say "${RED}NOT PRISTINE${RST}  $MOD"
  exit 1
fi

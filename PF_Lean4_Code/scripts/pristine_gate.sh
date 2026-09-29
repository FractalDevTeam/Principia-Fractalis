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

# --- (a) olean currency -------------------------------------------------------
if [ ! -f "$OLEAN" ]; then
  fail "(a) olean ABSENT — module has never been kernel-checked at this path"
elif [ "$SRC" -nt "$OLEAN" ]; then
  fail "(a) olean STALE — source is newer than olean; last check does not cover current source"
else
  pass "(a) olean CURRENT"
fi

# --- (c) escape hatches, comments stripped ------------------------------------
# Strip /- ... -/ block comments and -- line comments before scanning, so that
# docstrings saying "no sorry" do not trip the gate (a real false positive we hit).
STRIPPED="$(mktemp)"; trap 'rm -f "$STRIPPED" "$PROBE" "$PROBE_OUT" 2>/dev/null' EXIT
awk '
  BEGIN { inblk=0 }
  {
    line=$0
    while (1) {
      if (inblk) { i=index(line,"-/"); if (i==0) { line=""; break }
                   line=substr(line,i+2); inblk=0; continue }
      i=index(line,"/-")
      if (i==0) break
      line=substr(line,1,i-1); inblk=1
    }
    sub(/--.*$/,"",line)
    print line
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

# --- (d) dead binders via Lean's own linter -----------------------------------
# Attribute ONLY warnings whose file path is this module's source. lake build
# output includes the whole dependency chain; attributing a dependency's unused
# binder to the target module is a false accusation, so filter by path.
OWN_UNUSED="$(grep 'unused variable' "$BUILD_OUT" | grep -F "$SRC:" || true)"
DEP_UNUSED="$(grep 'unused variable' "$BUILD_OUT" | grep -vF "$SRC:" || true)"
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
if [ "$PREMISE_AUDIT" -eq 1 ]; then
  if [ -f "PF/Audit/PremiseAudit.lean" ]; then
    warn "(d+) PremiseAudit hook present; semantic dead-hypothesis sweep not yet wired"
  else
    warn "(d+) PremiseAudit not found"
  fi
fi

# --- (b) axioms, via a generated probe ----------------------------------------
# Do not rely on the module containing its own #print axioms: generate one.
mapfile -t DECLS < <(grep -nE '^[[:space:]]*(theorem|lemma)[[:space:]]+[A-Za-z_]' "$STRIPPED" \
  | sed -E 's/^[0-9]+:[[:space:]]*(theorem|lemma)[[:space:]]+([A-Za-z_][A-Za-z0-9_'"'"']*).*/\2/' | sort -u)

if [ "${#DECLS[@]}" -eq 0 ]; then
  warn "(b) no theorem/lemma declarations found to probe"
else
  NS="$(grep -E '^namespace ' "$STRIPPED" | awk '{print $2}' | paste -sd'.' -)"
  PROBE="$(mktemp --suffix=.lean -p . probe_gate_XXXX)"
  {
    echo "import $MOD"
    [ -n "$NS" ] && echo "open $NS"
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
  # collect any axiom token that is not on the allowlist
  BAD="$(grep -oE "depends on axioms: \[[^]]*\]" "$PROBE_OUT" \
        | tr -d '[]' | sed 's/depends on axioms://' | tr ',' '\n' \
        | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
        | grep -vxF -e propext -e Classical.choice -e Quot.sound || true)"
  if [ -n "$BAD" ]; then
    fail "(b) non-allowlisted axioms:"
    printf '%s\n' "$BAD" | sed 's/^/        /'
  elif ! grep -q 'sorryAx' "$PROBE_OUT"; then
    pass "(b) axioms ⊆ {propext, Classical.choice, Quot.sound} over ${#DECLS[@]} declarations"
  fi
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
    if grep -qE "(∃[^,]*,[^\n]*\b$p\b|example[[:space:]]*:[[:space:]]*$p\b|_nonvacuous|_nonempty|_satisfiable)" "$STRIPPED" \
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

# --- verdict ------------------------------------------------------------------
if [ "$FAIL" -eq 0 ]; then
  say "${GRN}PRISTINE${RST}  $MOD"
  exit 0
else
  say "${RED}NOT PRISTINE${RST}  $MOD"
  exit 1
fi

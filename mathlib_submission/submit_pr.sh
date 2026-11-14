#!/usr/bin/env bash
# Mathlib PR submission -- run FROM YOUR LAPTOP with gh authenticated.
#   ./submit_pr.sh pr5                -> Gram determinant => linear independence
#   ./submit_pr.sh pr7                -> Hilbert-Schmidt operators on l^2
#   ./submit_pr.sh pr8                -> compact transfer operators (AFTER pr7 exists)
#   ./submit_pr.sh not_fermat_42_sub  -> Fermat's n=4 difference form (a^4 - b^4 ≠ c^2)
# (pr6 TateLimit is intentionally absent: placement is waiting on the Zulip
#  thread "Tate's telescoping limit -- placement?"; submit after a reply.)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/.." && pwd)"
WORK="${MATHLIB_WORKDIR:-$HOME/mathlib4-pr}"

command -v gh >/dev/null || { echo "ERROR: gh not installed"; exit 1; }
gh auth status >/dev/null 2>&1 || { echo "ERROR: run 'gh auth login' first"; exit 1; }

case "${1:-}" in
  pr5)
    SRC="$REPO_ROOT/mathlib_candidates/GramLinearIndependent.lean"
    DST="Mathlib/LinearAlgebra/Matrix/GramLinearIndependent.lean"
    BRANCH="pc/gram-linear-independent"
    TITLE="feat(LinearAlgebra/Matrix): nonzero Gram determinant implies linear independence"
    ;;
  pr7)
    SRC="$REPO_ROOT/mathlib_candidates/HilbertSchmidt.lean"
    DST="Mathlib/Analysis/Normed/Operator/HilbertSchmidtL2.lean"
    BRANCH="pc/hilbert-schmidt-l2"
    TITLE="feat(Analysis/Normed/Operator): Hilbert-Schmidt operators on l2 are bounded and compact"
    ;;
  pr8)
    SRC="$REPO_ROOT/mathlib_candidates/TransferOperatorCompact.lean"
    DST="Mathlib/Analysis/Normed/Operator/TransferOperatorCompact.lean"
    BRANCH="pc/transfer-operator-compact"
    TITLE="feat(Analysis/Normed/Operator): transfer operators of contracting systems are compact"
    ;;
  not_fermat_42_sub)
    SRC="$REPO_ROOT/mathlib_candidates/NotFermat42Sub.lean"
    DST="Mathlib/NumberTheory/FLT/FourSub.lean"
    BRANCH="pc/not-fermat-42-sub"
    TITLE="feat(NumberTheory/FLT): Fermat n=4 difference form, \`a^4 - b^4 ≠ c^2\`"
    ;;
  *) echo "usage: $0 {pr5|pr7|pr8|not_fermat_42_sub}"; exit 1 ;;
esac

BODY_FILE="$HERE/body_${1}.md"
[ -f "$SRC" ] || { echo "ERROR: $SRC missing"; exit 1; }
[ -f "$BODY_FILE" ] || { echo "ERROR: $BODY_FILE missing"; exit 1; }

# fork + clone (idempotent)
if [ ! -d "$WORK/.git" ]; then
  gh repo fork leanprover-community/mathlib4 --clone=false >/dev/null 2>&1 || true
  ME="$(gh api user -q .login)"
  git clone --depth 1 "https://github.com/leanprover-community/mathlib4.git" "$WORK"
  git -C "$WORK" remote add fork "https://github.com/$ME/mathlib4.git"
fi
cd "$WORK"
git fetch origin master --depth 1
git checkout -B "$BRANCH" origin/master

# place the file; pr8 imports pr7's module under its mathlib name
mkdir -p "$(dirname "$DST")"
cp "$SRC" "$DST"
if [ "$1" = "pr8" ]; then
  sed -i.bak 's/^import HilbertSchmidt$/import Mathlib.Analysis.Normed.Operator.HilbertSchmidtL2/' "$DST" && rm -f "$DST.bak"
  # pr8 rides on pr7's branch content if pr7 is not yet merged:
  if ! git cat-file -e origin/master:Mathlib/Analysis/Normed/Operator/HilbertSchmidtL2.lean 2>/dev/null; then
    cp "$REPO_ROOT/mathlib_candidates/HilbertSchmidt.lean" Mathlib/Analysis/Normed/Operator/HilbertSchmidtL2.lean
    MODNAME_EXTRA="Mathlib.Analysis.Normed.Operator.HilbertSchmidtL2"
  fi
fi

# register module(s) in Mathlib.lean.  Module-system mathlib (>= v4.35) uses
# 'public import' lines after a 'module' header; the file must be
# byte-identical to what `lake exe mk_all` would generate (ASCII-sorted
# module-name block, 'Std' then 'Batteries' prepended, module-name
# aggregator excluded from its own import list).
#
# The previous sed-based insertion was not idempotent across re-runs and
# accumulated damage (deleted entries, reordered Std/Batteries, lost
# 'public meta' prefixes).  Use Python to do a clean "re-sort within the
# existing import block" insertion that preserves every other line.
MOD="$(echo "$DST" | sed 's#/#.#g; s#\.lean$##')"
for M in ${MODNAME_EXTRA:-} "$MOD"; do
  [ -z "$M" ] && continue
  # Already there in either plain or 'public import' form? Skip.
  grep -qE "^(public )?import $M$" Mathlib.lean && continue
  python3 - "$M" Mathlib.lean <<'PYEOF'
import sys
mod, path = sys.argv[1], sys.argv[2]
new_line = f"public import {mod}"
with open(path, "r", encoding="utf-8") as f:
    lines = f.read().splitlines()
# Find the 'public import' block.  mk_all orders these ascii-lex.
pub_indices = [i for i, l in enumerate(lines) if l.startswith("public import ")]
if not pub_indices:
    # Empty block: append after module header if present, else prepend.
    insert_at = 1 if lines and lines[0].startswith("module") else 0
else:
    # Insert BEFORE the first existing entry that sorts >= new_line.
    insert_at = pub_indices[-1] + 1
    for idx in pub_indices:
        if lines[idx] >= new_line:
            insert_at = idx
            break
lines.insert(insert_at, new_line)
with open(path, "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
PYEOF
done

git add -A
git commit -m "$TITLE"
git push -f fork "$BRANCH"
ME="$(gh api user -q .login)"
gh pr create --repo leanprover-community/mathlib4 \
  --head "$ME:$BRANCH" --title "$TITLE" --body-file "$BODY_FILE"
echo "DONE: PR opened for $1"

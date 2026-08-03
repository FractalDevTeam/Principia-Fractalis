#!/usr/bin/env bash
# Mathlib PR submission -- run FROM YOUR LAPTOP with gh authenticated.
#   ./submit_pr.sh pr5   -> Gram determinant => linear independence
#   ./submit_pr.sh pr7   -> Hilbert-Schmidt operators on l^2
#   ./submit_pr.sh pr8   -> compact transfer operators (AFTER pr7 exists)
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
  *) echo "usage: $0 {pr5|pr7|pr8}"; exit 1 ;;
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

# register module(s) in Mathlib.lean (sorted insert)
MOD="$(echo "$DST" | sed 's#/#.#g; s#\.lean$##')"
for M in ${MODNAME_EXTRA:-} "$MOD"; do
  [ -z "$M" ] && continue
  grep -qx "import $M" Mathlib.lean || {
    printf 'import %s\n' "$M" >> Mathlib.lean
    LC_ALL=C sort -o Mathlib.lean Mathlib.lean
  }
done

git add -A
git commit -m "$TITLE"
git push -f fork "$BRANCH"
ME="$(gh api user -q .login)"
gh pr create --repo leanprover-community/mathlib4 \
  --head "$ME:$BRANCH" --title "$TITLE" --body-file "$BODY_FILE"
echo "DONE: PR opened for $1"

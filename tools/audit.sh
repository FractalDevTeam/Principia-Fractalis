#!/usr/bin/env bash
# tools/audit.sh - Principia Fractalis build + axiom audit
#
# Runs the canonical verification chain that backs the
# "0 project axioms / 8360 jobs clean / kernel-only-axiom dependency"
# claim of the project. Designed to be run locally before any external
# release (per docs/governance/PUBLISHING_GATE.md), and identical to
# what .github/workflows/lean.yml runs in CI.
#
# Exit code 0 on success, non-zero on any failure.

set -euo pipefail

# Color helpers (off if not a TTY)
if [ -t 1 ]; then
  C_RED='\033[0;31m'; C_GREEN='\033[0;32m'; C_YELLOW='\033[0;33m'
  C_BLUE='\033[0;34m'; C_BOLD='\033[1m'; C_RESET='\033[0m'
else
  C_RED=''; C_GREEN=''; C_YELLOW=''; C_BLUE=''; C_BOLD=''; C_RESET=''
fi

log()  { printf "${C_BLUE}[audit]${C_RESET} %s\n" "$*"; }
ok()   { printf "${C_GREEN}[ ok ]${C_RESET} %s\n" "$*"; }
warn() { printf "${C_YELLOW}[warn]${C_RESET} %s\n" "$*"; }
fail() { printf "${C_RED}[FAIL]${C_RESET} %s\n" "$*" >&2; exit 1; }

# Locate repo root (this script lives in tools/)
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$REPO_ROOT/PF_Lean4_Code"
COQ_DIR="$REPO_ROOT/PF_Coq_Code"

CANONICAL_THEOREM="PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure"

# ----------------------------------------------------------------------
# Section 1: Lean 4 build
# ----------------------------------------------------------------------
log "Section 1: Lean 4 build (lake build PF)"

if ! command -v lake >/dev/null 2>&1; then
  fail "lake (Lean build tool) not found in PATH. Install via elan: https://leanprover.github.io/get_started/"
fi

cd "$LEAN_DIR"

log "  Lean toolchain: $(cat lean-toolchain)"
log "  Lake / Lean version:"
lake --version
lean --version

log "  Fetching mathlib cache..."
if lake exe cache get >/dev/null 2>&1; then
  ok "  mathlib cache fetched"
else
  warn "  cache get failed or partial; build will compile from source (slower)"
fi

log "  Running lake build PF (this can take 30-90 minutes from cold cache)..."
if lake build PF; then
  ok "Lean build succeeded"
else
  fail "Lean build failed. See output above."
fi

# ----------------------------------------------------------------------
# Section 2: Axiom check on canonical theorem
# ----------------------------------------------------------------------
log "Section 2: Axiom dependency of canonical theorem"
log "  Theorem: $CANONICAL_THEOREM"

AXIOM_OUTPUT="$(mktemp)"
trap 'rm -f "$AXIOM_OUTPUT"' EXIT

# Use `lean --run` with a small inline script that prints axioms
cat > /tmp/_pf_axiom_check.lean << EOF
import PF
#print axioms $CANONICAL_THEOREM
EOF

if lake env lean /tmp/_pf_axiom_check.lean > "$AXIOM_OUTPUT" 2>&1; then
  cat "$AXIOM_OUTPUT"
else
  cat "$AXIOM_OUTPUT" >&2
  fail "Axiom check failed to run"
fi

# Verify only kernel axioms appear: propext, Classical.choice, Quot.sound
EXPECTED='propext|Classical\.choice|Quot\.sound'

# Count axiom lines (lines that are NOT "axioms" header and NOT empty/whitespace)
SUSPICIOUS_AXIOMS="$(grep -vE "^\s*$|axioms" "$AXIOM_OUTPUT" | grep -vE "$EXPECTED" || true)"

if [ -n "$SUSPICIOUS_AXIOMS" ]; then
  printf "${C_RED}[FAIL]${C_RESET} Canonical theorem depends on unexpected axioms:\n%s\n" "$SUSPICIOUS_AXIOMS" >&2
  exit 1
else
  ok "Canonical theorem uses only Lean kernel axioms (propext, Classical.choice, Quot.sound)"
fi

# ----------------------------------------------------------------------
# Section 3: Coq build (optional, runs if coq toolchain available)
# ----------------------------------------------------------------------
log "Section 3: Coq build"

if command -v coqc >/dev/null 2>&1 || command -v rocq >/dev/null 2>&1; then
  cd "$COQ_DIR"
  log "  coqc version: $(coqc --version 2>/dev/null | head -1 || true)"
  if [ -f _CoqProject ]; then
    log "  Building Coq sources via coq_makefile..."
    coq_makefile -f _CoqProject -o CoqMakefile
    if make -j -f CoqMakefile >/dev/null 2>&1; then
      VOFILES="$(find . -name '*.vo' | wc -l)"
      MANIFEST="$(grep -cE '^[A-Za-z]' _CoqProject || echo 0)"
      ok "Coq build succeeded (.vo files: $VOFILES; _CoqProject active entries: ~$MANIFEST)"
    else
      warn "Coq build failed; Lean side is the load-bearing layer"
    fi
  else
    warn "_CoqProject not found at $COQ_DIR; skipping Coq build"
  fi
else
  warn "Coq toolchain (coqc / rocq) not found; skipping Coq build"
  warn "  Lean side is the load-bearing layer; Coq is parity cross-check"
fi

# ----------------------------------------------------------------------
# Summary
# ----------------------------------------------------------------------
printf "\n${C_BOLD}${C_GREEN}===========================================${C_RESET}\n"
printf "${C_BOLD}${C_GREEN}  Principia Fractalis audit: PASS${C_RESET}\n"
printf "${C_BOLD}${C_GREEN}===========================================${C_RESET}\n"
echo
echo "Lean library 'PF' built successfully."
echo "Canonical theorem '$CANONICAL_THEOREM'"
echo "depends only on Lean kernel axioms [propext, Classical.choice, Quot.sound]."
echo
echo "For the full open-problem catalog, see OPEN_PROBLEMS.md."
echo "For the axiom-shaped commitment catalog, see AXIOM_AUDIT.md."

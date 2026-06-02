#!/usr/bin/env bash
# Principia Fractalis Referee Audit Script
# Anchor commit: 2cfde50 (HEAD as of 2026-06-02)
#
# Usage:
#   bash tools/audit.sh
#
# Prints:
#   1. Current commit hash
#   2. Git status
#   3. Lean build result + job count
#   4. Per-capstone #print axioms output
#   5. Coq parity stub compile result
#
# Run from the repo root.

set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

ELAN_PATH="$HOME/.elan/bin"
if [ -d "$ELAN_PATH" ]; then
  export PATH="$ELAN_PATH:$PATH"
fi

echo "============================================================"
echo "PRINCIPIA FRACTALIS - REFEREE AUDIT"
echo "============================================================"
echo

echo "-- 1. Repository state --"
echo "Commit:   $(git rev-parse HEAD)"
echo "Branch:   $(git rev-parse --abbrev-ref HEAD)"
echo "Status:"
git status --short | sed 's/^/   /'
echo

echo "-- 2. Lean build --"
echo "Building PF (full closure of PF.lean) ..."
cd PF_Lean4_Code
LEAN_OUT=$(lake build PF 2>&1 | tail -3)
echo "$LEAN_OUT" | sed 's/^/   /'
echo

echo "-- 3. Lean per-capstone axiom audit --"
echo "(Running PF/Referee/CapstoneDependencyAudit.lean ...)"
AUDIT_OUT=$(lake env lean PF/Referee/CapstoneDependencyAudit.lean 2>&1)
echo "$AUDIT_OUT" | grep -E "depends on axioms|does not depend on any axioms" | sed 's/^/   /'
echo

cd "$REPO_ROOT"

echo "-- 4. Coq parity stub --"
if command -v coqc >/dev/null 2>&1; then
  echo "Compiling PF_Coq_Code/PF/Referee/RefereeIndex.v ..."
  cd PF_Coq_Code
  COQ_OUT=$(coqc -Q PF PrincipiaTractalis PF/Referee/RefereeIndex.v 2>&1)
  if [ -z "$COQ_OUT" ]; then
    echo "   Compiled clean (no output, .vo produced)"
    ls -la PF/Referee/RefereeIndex.vo 2>&1 | sed 's/^/   /'
  else
    echo "$COQ_OUT" | sed 's/^/   /'
  fi
  cd "$REPO_ROOT"
else
  echo "   coqc not found in PATH; skipping Coq parity check"
fi
echo

echo "-- 5. Single citation theorem check --"
cd PF_Lean4_Code
echo "Checking PF.Referee.RefereeIndex.refereeLayerAtHEAD_05ac9b5_realised ..."
CITE_OUT=$(lake env lean PF/Referee/RefereeIndex.lean 2>&1)
echo "$CITE_OUT" | grep -E "refereeLayerAtHEAD" | sed 's/^/   /'
echo

cd "$REPO_ROOT"

echo "============================================================"
echo "Audit complete."
echo "Reference: PROOF_PACKAGE.md (this repo root)"
echo "Single-citation theorem: PF.Referee.RefereeIndex.refereeLayerAtHEAD_05ac9b5_realised"
echo "============================================================"

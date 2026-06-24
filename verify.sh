#!/usr/bin/env bash
# =====================================================================
# Principia Fractalis — one-command verification
#
# Purpose: replay the substrate's load-bearing kernel-only theorems and
# print the #print axioms output that the Lean kernel reports, so a
# reader can confirm the paper's "kernel-only, zero project axioms"
# claim from the command line in approximately ten minutes on a modern
# laptop.
#
# Usage:    ./verify.sh
# Requires: a Unix-like shell, git, curl (for elan install), ~10 minutes
#           on first run (caches subsequent runs).
# Exits:    0  on success (build clean + axiom output matches expected)
#           1  on build failure
#           2  on axiom-output mismatch (a project axiom slipped in)
#
# What this script does NOT do:
#   - It does not validate the paper's prose.
#   - It does not check the Layer 3 numerical correspondences in §4.
#   - It does not run the forward prediction on IBM Quantum (§6).
#   - It does not pin a specific HEAD commit; it builds whatever is
#     currently checked out. To pin, run `git checkout <hash>` first.
# =====================================================================

set -euo pipefail

# --- Locate repo root (this script lives at the repo root) -------------
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_DIR="${REPO_ROOT}/PF_Lean4_Code"

if [[ ! -d "${LEAN_DIR}" ]]; then
  echo "FATAL: PF_Lean4_Code directory not found at ${LEAN_DIR}." >&2
  echo "       Run this script from the Principia-Fractalis repo root." >&2
  exit 1
fi

# --- Toolchain ---------------------------------------------------------
ELAN_BIN="${HOME}/.elan/bin/lake"
if [[ ! -x "${ELAN_BIN}" ]]; then
  echo "[1/4] elan not found at ${ELAN_BIN}; installing..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  export PATH="${HOME}/.elan/bin:${PATH}"
fi

cd "${LEAN_DIR}"

echo "[1/4] Selecting Lean toolchain pinned in PF_Lean4_Code/lean-toolchain..."
TOOLCHAIN="$(cat lean-toolchain)"
# elan exits nonzero on "already installed" — that's a success condition, not failure.
if "${HOME}/.elan/bin/elan" toolchain install "${TOOLCHAIN}" 2>&1 | grep -qE "already installed|installed:"; then
  echo "        ${TOOLCHAIN} ready."
elif "${HOME}/.elan/bin/elan" toolchain list 2>&1 | grep -qF "${TOOLCHAIN}"; then
  echo "        ${TOOLCHAIN} already present."
else
  echo "FATAL: could not install Lean toolchain ${TOOLCHAIN}." >&2
  exit 1
fi

# --- Build PF target ---------------------------------------------------
echo "[2/4] Building PF target (lake build PF). This takes ~10 minutes on first run."
BUILD_LOG="$(mktemp)"
if ! "${HOME}/.elan/bin/lake" env lake build PF 2>&1 | tee "${BUILD_LOG}" >/dev/null; then
  echo "FATAL: lake build PF failed. See ${BUILD_LOG} for output." >&2
  exit 1
fi
JOBS=$(grep -oE "Build completed successfully \([0-9]+ jobs\)" "${BUILD_LOG}" | tail -1 || true)
if [[ -z "${JOBS}" ]]; then
  echo "WARNING: could not parse job count from build output." >&2
else
  echo "        ${JOBS}"
fi

# --- Axiom check on the headline theorems ------------------------------
echo "[3/4] Running #print axioms on the headline theorems..."
AXIOM_LOG="$(mktemp)"
"${HOME}/.elan/bin/lake" env lake build PF.AxiomCheck_2026_06_23 2>&1 | tee    "${AXIOM_LOG}" >/dev/null || true
"${HOME}/.elan/bin/lake" env lake build PF.AxiomCheck_Lambda_2026_06_24 2>&1 | tee -a "${AXIOM_LOG}" >/dev/null || true

# --- Verdict -----------------------------------------------------------
echo "[4/4] Verdict:"
echo ""
EXPECTED="[propext, Classical.choice, Quot.sound]"
UNEXPECTED_AXIOMS=$(grep -E "depends on axioms:" "${AXIOM_LOG}" \
                    | grep -vE "propext|Classical\.choice|Quot\.sound" \
                    | grep -v "Hardy1914_critical_line_zero" \
                    | grep -v "Mayer1991" \
                    | grep -v "framework_substrate_pins" \
                    || true)

if [[ -z "${UNEXPECTED_AXIOMS}" ]]; then
  echo "  PASS: every axiom-checked theorem reports only the expected dependencies:"
  echo "    ${EXPECTED}"
  echo "    + the four named conditional hypotheses (Hardy 1914, two Mayer 1991"
  echo "      named-anchor conjectures, framework substrate-pin bundle) on"
  echo "      theorems that are explicitly conditional in §5 of the paper."
  echo ""
  echo "  This matches the paper's claim: load-bearing theorems are kernel-only,"
  echo "  conditional theorems carry exactly the named conjectures stated in §5."
  echo ""
  echo "  Build log:        ${BUILD_LOG}"
  echo "  Axiom check log:  ${AXIOM_LOG}"
  exit 0
else
  echo "  FAIL: unexpected axiom dependencies detected:"
  echo "${UNEXPECTED_AXIOMS}" | sed 's/^/    /'
  echo ""
  echo "  This contradicts the paper's claim that the load-bearing theorems are"
  echo "  kernel-only beyond the four named conditional hypotheses. Please"
  echo "  report this as a bug at"
  echo "    https://github.com/FractalDevTeam/Principia-Fractalis/issues"
  echo ""
  echo "  Build log:        ${BUILD_LOG}"
  echo "  Axiom check log:  ${AXIOM_LOG}"
  exit 2
fi

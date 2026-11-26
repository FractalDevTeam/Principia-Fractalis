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
#           PF_VERIFY_SELFTEST=1 ./verify.sh    # ~1s, no build: proves
#                                               # the gate can fail
# Requires: a Unix-like shell, git, curl (for elan install), ~10 minutes
#           on first run (caches subsequent runs).
# Exits:    0  PASS   — build clean, every axiom dependency permitted
#           1  BUILD  — toolchain, build, or axiom-check build failed
#           2  FAIL   — an axiom outside the permitted set appeared
#           3  INCONCLUSIVE — the gate could not gather evidence
#                      (empty axiom log, or a truncated axiom list whose
#                      unseen names cannot be ruled out). Never PASS.
#
# What this script does NOT do:
#   - It does not validate the paper's prose.
#   - It does not check the Layer 3 numerical correspondences in §4.
#   - It does not run the forward prediction on IBM Quantum (§6).
#   - It does not pin a specific HEAD commit; it builds whatever is
#     currently checked out. To pin, run `git checkout <hash>` first.
#
# ---------------------------------------------------------------------
# AXIOM CONTRACT (the thing this gate actually enforces)
#
#   Category A — kernel axioms. Always permitted, reported silently:
#       propext, Classical.choice, Quot.sound
#
#   Category B — named citation axioms. Permitted, but every occurrence
#   is LISTED in the output with the theorem that carries it, so a
#   reader sees exactly which results are conditional and on what:
#       Hardy1914_published_theorem_substrate_citation
#       Mayer1991_Cohen2025_substrate_HP_program_citation
#       Mayer1991_Cohen2025_T3_sym_HP_program_citation
#       framework_substrate_pins_bulletproof_bundle
#
#   Category C — everything else, `sorryAx` and any project-level
#   `axiom` declaration included. Any single occurrence is a FAIL.
#
# Category B is the contract this script inherited; it is reported, not
# hidden. If the project's intent is that NO citation axiom remains on
# any axiom-checked theorem, empty the CITATION_AXIOMS array below and
# the gate will enforce that stricter contract immediately.
#
# 2026-11-16 repair note. The previous verdict block filtered the axiom
# log line-by-line with `grep -vE "propext|..."`. Every `#print axioms`
# line contains `propext`, so that pipeline deleted every line it was
# meant to inspect, including a line that also carried `sorryAx`: the
# unexpected-axiom list was unconditionally empty and `exit 2` was
# unreachable. The gate could not fail on axiom content. It now tokenises
# each line and tests each axiom name individually, and the self-test
# below replays that exact regression.
#
# A second defect of the same shape was found while testing the repair
# against the real probe logs in codex/: `#print axioms` wraps long
# lists across physical lines, so reading line-by-line saw only
# "[propext," and would have passed a theorem whose `sorryAx` sat on a
# continuation line. Records are now joined before inspection, and a
# record whose bracket never closes is INCONCLUSIVE rather than clean.
# Synthetic tests alone did not expose this; real output did.
# =====================================================================

set -euo pipefail

# --- The axiom contract, as data ---------------------------------------
KERNEL_AXIOMS=(propext Classical.choice Quot.sound)
CITATION_AXIOMS=(
  Hardy1914_published_theorem_substrate_citation
  Mayer1991_Cohen2025_substrate_HP_program_citation
  Mayer1991_Cohen2025_T3_sym_HP_program_citation
  framework_substrate_pins_bulletproof_bundle
)

# --- Verdict machinery -------------------------------------------------
# Deliberately separated from the build so it is testable without Lean.

in_list() {
  local needle="$1"; shift
  local item
  for item in "$@"; do
    [[ "${item}" == "${needle}" ]] && return 0
  done
  return 1
}

# in_list_suffix <needle> <item>...
#   True iff <needle> equals some <item>, or ends in `.<item>`. Lean prints
#   axiom names fully qualified (e.g. `PF.Analytic.RH_x.Hardy1914_...`), while
#   the citation whitelist carries bare names. A plain `==` would miss every
#   real-world match; this is what the audit of 2026-11-17 found by running
#   the classifier against Papers/axiom_check_output_HEAD.txt.
in_list_suffix() {
  local needle="$1"; shift
  local item
  for item in "$@"; do
    [[ "${needle}" == "${item}" || "${needle}" == *".${item}" ]] && return 0
  done
  return 1
}

# normalize_axiom_log <logfile>
#   `#print axioms` WRAPS long axiom lists across several physical lines:
#
#       'Foo.bar' depends on axioms: [propext,
#          Some.Other.Axiom, Quot.sound]
#
#   so a per-physical-line reader sees only `[propext,` and declares the
#   theorem clean while the offending name sits on a continuation line.
#   This was found by running the classifier against the real probe logs
#   in codex/ — the synthetic cases alone did not expose it, which is the
#   whole reason to test against real output.
#
#   Emits one joined record per axiom report, on a single line.
normalize_axiom_log() {
  awk '
    /depends on axioms:/ {
      if (inrec) { print rec }
      rec = $0; inrec = 1
      if (rec ~ /\]/) { print rec; inrec = 0 }
      next
    }
    inrec {
      rec = rec " " $0
      if ($0 ~ /\]/) { print rec; inrec = 0 }
      next
    }
    END { if (inrec) print rec }
  ' "$1"
}

# classify_axiom_log <logfile>
#   Populates the globals:
#     CLASSIFIED_LINES     count of axiom reports inspected (joined)
#     CLASSIFIED_OFFENDERS array of "decl -> axiom" for Category C
#     CLASSIFIED_CITATIONS array of "decl -> axiom" for Category B
#     CLASSIFIED_TRUNCATED count of reports with no closing bracket
#   Returns 0 always; the caller reads the globals and decides.
classify_axiom_log() {
  local log="$1"
  local line decl axioms tok
  local -a toks
  CLASSIFIED_LINES=0
  CLASSIFIED_OFFENDERS=()
  CLASSIFIED_CITATIONS=()
  CLASSIFIED_TRUNCATED=0

  while IFS= read -r line; do
    CLASSIFIED_LINES=$((CLASSIFIED_LINES + 1))
    # Strip the trailing `' depends on axioms:...` and the leading
    # `info: file:line:col: '` that `lake build` adds in CI output.
    decl="${line%\' depends on axioms:*}"
    decl="${decl##*\'}"
    # A record with no closing bracket is a truncated log, not a clean
    # theorem. Count it so the caller can refuse to call it a pass.
    [[ "${line}" != *"]"* ]] && CLASSIFIED_TRUNCATED=$((CLASSIFIED_TRUNCATED + 1))
    axioms="${line#*depends on axioms: }"
    axioms="${axioms#\[}"
    axioms="${axioms%%\]*}"
    IFS=',' read -r -a toks <<< "${axioms}"
    for tok in "${toks[@]}"; do
      tok="$(printf '%s' "${tok}" | tr -d '[:space:]')"
      # Skip empties and pure-punctuation fragments (e.g. an elided
      # "..." in hand-written prose rather than machine output).
      [[ -z "${tok}" ]] && continue
      [[ "${tok}" != *[A-Za-z0-9]* ]] && continue
      if in_list "${tok}" "${KERNEL_AXIOMS[@]}"; then
        continue
      elif [[ ${#CITATION_AXIOMS[@]} -gt 0 ]] && in_list_suffix "${tok}" "${CITATION_AXIOMS[@]}"; then
        CLASSIFIED_CITATIONS+=("${decl} -> ${tok}")
      else
        CLASSIFIED_OFFENDERS+=("${decl} -> ${tok}")
      fi
    done
  done < <(normalize_axiom_log "${log}")

  return 0
}

# --- Self-test: proves the gate can fail, in about one second ----------
# Runs the real classifier against synthetic logs, including the exact
# line shape the 2026-11-16 repair note describes.
if [[ "${PF_VERIFY_SELFTEST:-0}" == "1" ]]; then
  echo "PF verify.sh self-test (classifier only; no Lean build)"
  echo ""
  st_tmp="$(mktemp -d)"
  st_fail=0

  st_case() {
    local name="$1" expect_offenders="$2" expect_citations="$3" expect_lines="$4" body="$5"
    local expect_trunc="${6:-0}"
    local f="${st_tmp}/${name}.log"
    printf '%s' "${body}" > "${f}"
    classify_axiom_log "${f}"
    local got_o=${#CLASSIFIED_OFFENDERS[@]} got_c=${#CLASSIFIED_CITATIONS[@]}
    if [[ "${got_o}" == "${expect_offenders}" && "${got_c}" == "${expect_citations}" \
          && "${CLASSIFIED_LINES}" == "${expect_lines}" \
          && "${CLASSIFIED_TRUNCATED}" == "${expect_trunc}" ]]; then
      printf '  ok   %-28s offenders=%s citations=%s records=%s trunc=%s\n' \
        "${name}" "${got_o}" "${got_c}" "${CLASSIFIED_LINES}" "${CLASSIFIED_TRUNCATED}"
    else
      printf '  FAIL %-28s offenders=%s (want %s) citations=%s (want %s) records=%s (want %s) trunc=%s (want %s)\n' \
        "${name}" "${got_o}" "${expect_offenders}" "${got_c}" "${expect_citations}" \
        "${CLASSIFIED_LINES}" "${expect_lines}" "${CLASSIFIED_TRUNCATED}" "${expect_trunc}"
      st_fail=1
    fi
  }

  st_case clean-three 0 0 1 \
"'PF.Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]
"
  # The regression: sorryAx on a line that ALSO contains propext. The old
  # grep -v pipeline deleted this line and reported PASS.
  st_case sorryax-beside-propext 1 0 1 \
"'PF.Foo.baz' depends on axioms: [propext, sorryAx]
"
  st_case project-axiom 1 0 1 \
"'PF.Foo.qux' depends on axioms: [propext, Classical.choice, PF.MyProjectAxiom]
"
  st_case named-citation 0 1 1 \
"'PF.RH.cond' depends on axioms: [propext, Hardy1914_published_theorem_substrate_citation]
"
  st_case mixed-citation-and-sorry 1 1 2 \
"'PF.RH.cond' depends on axioms: [propext, Mayer1991_Cohen2025_substrate_HP_program_citation]
'PF.Bad.thm' depends on axioms: [Quot.sound, sorryAx]
"
  st_case no-axioms-line 0 0 0 \
"'PF.Foo.pure' does not depend on any axioms
"
  st_case empty-log 0 0 0 ""

  # Wrapped output. `#print axioms` breaks long lists across lines; a
  # per-physical-line reader sees only "[propext," and calls it clean.
  st_case wrapped-clean 0 0 1 \
"'PF.Foo.wrap' depends on axioms: [propext,
   Classical.choice, Quot.sound]
"
  # The second regression: sorryAx on a CONTINUATION line.
  st_case wrapped-sorryax 1 0 1 \
"'PF.Foo.wrapbad' depends on axioms: [propext,
   sorryAx, Quot.sound]
"
  # The real shape, taken verbatim from codex/hodge_archive_inconsistency_probe_output.txt
  st_case wrapped-archive-axiom 1 0 1 \
"'HodgeArchiveProbe.archive_axiom_is_inconsistent' depends on axioms: [propext,
   HodgeArchiveProbe.concentration_implies_algebraic, Quot.sound]
"
  st_case wrapped-two-records 1 1 2 \
"'PF.A' depends on axioms: [propext,
   Hardy1914_published_theorem_substrate_citation]
'PF.B' depends on axioms: [Quot.sound,
   PF.SomeProjectAxiom]
"
  # Truncated log: the list never closes. Not a clean theorem.
  st_case truncated-record 0 0 1 \
"'PF.Foo.cut' depends on axioms: [propext,
" 1
  # Citation on a module-qualified name — the real Lean output shape.
  # Bare-name whitelist must match via dotted-suffix, else legitimate
  # citations get misclassified as Category C violations. Audit 2026-11-17.
  st_case citation-module-qualified 0 1 1 \
"'PF.RH.cond' depends on axioms: [propext, PF.Foo.Hardy1914_published_theorem_substrate_citation]
"
  # The real `info: file:line:col: '...':` prefix shape, as produced by
  # `lake build` in CI (see Papers/axiom_check_output_HEAD.txt). Exercises
  # both the decl-stripping and the dotted-suffix citation match on a
  # wrapped multi-line record.
  st_case real-info-prefix-wrapped 0 1 1 \
"info: PF/AxiomCheck_2026_06_23.lean:14:0: 'PF.Analytic.RH_x.clay_riemann_hypothesis_standard_framework_standard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PF.Analytic.RH_x.Hardy1914_published_theorem_substrate_citation]
"

  rm -rf "${st_tmp}"
  echo ""
  if [[ "${st_fail}" == "0" ]]; then
    echo "  self-test PASS — the classifier detects sorryAx and project axioms,"
    echo "  permits the kernel three, and reports named citation axioms separately."
    echo "  An empty log yields zero evidence lines, which the gate treats as"
    echo "  INCONCLUSIVE (exit 3), never as PASS."
    exit 0
  else
    echo "  self-test FAILED — do not trust this gate until it is fixed." >&2
    exit 1
  fi
fi

# --- Classify-only mode: apply the contract to an existing log ---------
# PF_VERIFY_CLASSIFY=<file> ./verify.sh
# Runs the same classifier and the same exit-code contract against an
# axiom log captured earlier (e.g. the output of
# `lake env lean PF/AxiomCheck_All_2026_06_25.lean`), with no build. Lets
# a reader re-check a saved log, and lets the gate be exercised against
# real output rather than only synthetic cases.
if [[ -n "${PF_VERIFY_CLASSIFY:-}" ]]; then
  if [[ ! -f "${PF_VERIFY_CLASSIFY}" ]]; then
    echo "FATAL: no such log: ${PF_VERIFY_CLASSIFY}" >&2
    exit 1
  fi
  classify_axiom_log "${PF_VERIFY_CLASSIFY}"
  echo "Axiom contract applied to: ${PF_VERIFY_CLASSIFY}"
  echo "  axiom reports inspected : ${CLASSIFIED_LINES}"
  echo "  truncated reports       : ${CLASSIFIED_TRUNCATED}"
  echo "  Category B (citation)   : ${#CLASSIFIED_CITATIONS[@]}"
  echo "  Category C (violations) : ${#CLASSIFIED_OFFENDERS[@]}"
  if [[ ${#CLASSIFIED_CITATIONS[@]} -gt 0 ]]; then
    echo ""
    echo "  Conditional on named citation axioms:"
    printf '    %s\n' "${CLASSIFIED_CITATIONS[@]}"
  fi
  if [[ ${#CLASSIFIED_OFFENDERS[@]} -gt 0 ]]; then
    echo ""
    echo "  FAIL — outside the contract:"
    printf '    %s\n' "${CLASSIFIED_OFFENDERS[@]}"
    exit 2
  fi
  if [[ "${CLASSIFIED_LINES}" -eq 0 ]]; then
    echo ""
    echo "  INCONCLUSIVE — no axiom reports in this log. Not a pass."
    exit 3
  fi
  if [[ "${CLASSIFIED_TRUNCATED}" -gt 0 ]]; then
    echo ""
    echo "  INCONCLUSIVE — ${CLASSIFIED_TRUNCATED} report(s) truncated. Not a pass."
    exit 3
  fi
  echo ""
  echo "  PASS — every inspected dependency is permitted."
  exit 0
fi

# --- Locate repo root (this script lives at the repo root) -------------
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_DIR="${REPO_ROOT}/PF_Lean4_Code"

if [[ ! -d "${LEAN_DIR}" ]]; then
  echo "FATAL: PF_Lean4_Code directory not found at ${LEAN_DIR}." >&2
  echo "       Run this script from the Principia-Fractalis repo root." >&2
  exit 1
fi

# --- Toolchain ---------------------------------------------------------
# Network and installer failures here are environment failures, not
# mathematical ones, and they get their own diagnostic. Three of the six
# CI failures on record died in this block in under 16 seconds with no
# message, because `curl | sh` under `set -o pipefail` aborts the script
# silently.
LAKE_BIN="${HOME}/.elan/bin/lake"
ELAN_CMD="${HOME}/.elan/bin/elan"

if [[ ! -x "${LAKE_BIN}" ]]; then
  echo "[1/5] elan not found at ${LAKE_BIN}; installing..."
  ELAN_INIT="$(mktemp)"
  if ! curl -sSf --retry 3 --retry-delay 5 --retry-connrefused --max-time 120 \
         https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
         -o "${ELAN_INIT}"; then
    rc=$?
    echo "FATAL: could not download the elan installer (curl exit ${rc})." >&2
    echo "       This is an environment/network failure, not a verification" >&2
    echo "       failure: nothing about the mathematics has been checked yet." >&2
    exit 1
  fi
  if ! sh "${ELAN_INIT}" -y --default-toolchain none; then
    rc=$?
    echo "FATAL: the elan installer failed (exit ${rc})." >&2
    echo "       Environment failure; no mathematics has been checked yet." >&2
    exit 1
  fi
  rm -f "${ELAN_INIT}"
  export PATH="${HOME}/.elan/bin:${PATH}"
fi

if [[ ! -x "${ELAN_CMD}" ]]; then
  echo "FATAL: elan is not executable at ${ELAN_CMD} after installation." >&2
  exit 1
fi

cd "${LEAN_DIR}"

echo "[1/5] Selecting Lean toolchain pinned in PF_Lean4_Code/lean-toolchain..."
TOOLCHAIN="$(cat lean-toolchain)"
# elan exits nonzero on "already installed" — that's a success condition, not failure.
if "${ELAN_CMD}" toolchain install "${TOOLCHAIN}" 2>&1 | grep -qE "already installed|installed:"; then
  echo "        ${TOOLCHAIN} ready."
elif "${ELAN_CMD}" toolchain list 2>&1 | grep -qF "${TOOLCHAIN}"; then
  echo "        ${TOOLCHAIN} already present."
else
  echo "FATAL: could not install Lean toolchain ${TOOLCHAIN}." >&2
  echo "       Environment failure; no mathematics has been checked yet." >&2
  exit 1
fi

# --- Fetch the prebuilt mathlib cache ----------------------------------
# Without this the runner COMPILES MATHLIB FROM SOURCE, which alone exceeds the
# job budget; the workflow had no cache step at all before 2026-11-25. This is
# an optimisation, never a correctness condition: the oleans it downloads are
# mathlib's own CI artifacts for the revision pinned in lake-manifest.json, and
# if the fetch fails we fall through and build from source instead. So a cache
# miss makes the gate SLOW, it can never make the gate WRONG.
echo "[2/4] Fetching prebuilt mathlib cache (lake exe cache get)..."
if "${LAKE_BIN}" exe cache get 2>&1 | tail -3; then
  echo "        mathlib cache ready."
else
  echo "        WARNING: cache fetch failed; mathlib will build from source." >&2
  echo "        This is slow but not a verification failure." >&2
fi

# --- Build the PF closure ----------------------------------------------
# PFClosure, not PF. The `PF` lean_lib is declared with globs = ["PF.+"], so it
# is ALL ~10,870 modules including the ~1,260 standalone leaf panels -- ~400s
# each, and the AssemblePart c=829/64 ones need about 13.6 GB of live data. That
# cannot complete inside a 6-hour job, which is why this gate has never
# reported a verdict on master.
#
# PFClosure has `roots = ["PF"]` and no globs, so it is PF.lean and its
# transitive imports: the 1,641-module closure, measured 2026-11-25 as having
# ZERO missing modules. That closure is what every book citation and every
# headline theorem actually lives in, and it is what a referee re-checks.
#
# SCOPE, stated plainly: the leaf panels are NOT covered by this gate. They are
# additional numerical evidence, built on Legion/Acer, and nothing in the book
# or the closure imports them.
echo "[3/5] Building the PF closure (lake build +PF:olean)..."
BUILD_LOG="$(mktemp)"
if ! "${LAKE_BIN}" env lake build +PF:olean 2>&1 | tee "${BUILD_LOG}" >/dev/null; then
  echo "FATAL: lake build +PF:olean failed. See ${BUILD_LOG} for output." >&2
  tail -40 "${BUILD_LOG}" >&2 || true
  exit 1
fi
JOBS=$(grep -oE "Build completed successfully \([0-9]+ jobs\)" "${BUILD_LOG}" | tail -1 || true)
if [[ -z "${JOBS}" ]]; then
  echo "WARNING: could not parse job count from build output." >&2
else
  echo "        ${JOBS}"
fi

# --- Axiom check on the headline theorems ------------------------------
# Each checker module must BUILD. A checker that fails to build emits no
# `depends on axioms:` lines, and an empty log must never be mistaken for
# a clean one — that is how a failed build comes to print a clean axiom
# bar. So a checker build failure is exit 1, and an empty log is exit 3.
echo "[4/5] Running #print axioms on the headline theorems..."
AXIOM_LOG="$(mktemp)"
AXIOM_MODULES=(
  PF.AxiomCheck_2026_06_23
  PF.AxiomCheck_Lambda_2026_06_24
  PF.AxiomCheck_All_2026_06_25
)
checker_failed=0
for mod in "${AXIOM_MODULES[@]}"; do
  if ! "${LAKE_BIN}" env lake build "${mod}:olean" 2>&1 | tee -a "${AXIOM_LOG}" >/dev/null; then
    echo "FATAL: axiom-check module ${mod} failed to build." >&2
    checker_failed=1
  fi
done
if [[ "${checker_failed}" != "0" ]]; then
  echo "       The gate refuses to report a verdict from a checker that did not" >&2
  echo "       build: an unbuilt checker prints no axioms, which would read as" >&2
  echo "       a clean bar. See ${AXIOM_LOG}." >&2
  exit 1
fi

# --- Verdict -----------------------------------------------------------
echo "[5/5] Verdict:"
echo ""
EXPECTED="[propext, Classical.choice, Quot.sound]"

classify_axiom_log "${AXIOM_LOG}"

if [[ "${CLASSIFIED_LINES}" -eq 0 ]]; then
  echo "  INCONCLUSIVE: the axiom-check modules built, but the log contains no"
  echo "  '#print axioms' output at all. Nothing was verified."
  echo ""
  echo "  This is not a pass. Check that ${AXIOM_MODULES[*]}"
  echo "  still contain '#print axioms' commands."
  echo ""
  echo "  Build log:        ${BUILD_LOG}"
  echo "  Axiom check log:  ${AXIOM_LOG}"
  exit 3
fi

if [[ ${#CLASSIFIED_OFFENDERS[@]} -gt 0 ]]; then
  echo "  FAIL: ${#CLASSIFIED_OFFENDERS[@]} axiom dependency/dependencies outside the"
  echo "  permitted contract:"
  printf '    %s\n' "${CLASSIFIED_OFFENDERS[@]}"
  echo ""
  echo "  'sorryAx' here means an incomplete proof reached an axiom-checked"
  echo "  theorem. Any other name is a project-level axiom that the paper's"
  echo "  kernel-only claim does not cover."
  echo ""
  echo "  Please report this at"
  echo "    https://github.com/FractalDevTeam/Principia-Fractalis/issues"
  echo ""
  echo "  Build log:        ${BUILD_LOG}"
  echo "  Axiom check log:  ${AXIOM_LOG}"
  exit 2
fi

if [[ "${CLASSIFIED_TRUNCATED}" -gt 0 ]]; then
  echo "  INCONCLUSIVE: ${CLASSIFIED_TRUNCATED} axiom report(s) have no closing bracket,"
  echo "  so the axiom list was cut off and unseen names may remain."
  echo ""
  echo "  A truncated log is not a clean one. Re-run with the full output"
  echo "  preserved; see ${AXIOM_LOG}."
  echo ""
  echo "  Build log:        ${BUILD_LOG}"
  exit 3
fi

  echo "  PASS: ${CLASSIFIED_LINES} axiom-checked theorem(s) inspected, token by token"
  echo "  (wrapped multi-line axiom lists are joined before inspection)."
  echo "  Every dependency is permitted:"
  echo "    ${EXPECTED}"
  if [[ ${#CLASSIFIED_CITATIONS[@]} -gt 0 ]]; then
    echo ""
    echo "  Plus ${#CLASSIFIED_CITATIONS[@]} named citation-axiom dependency/dependencies."
    echo "  These theorems are CONDITIONAL on the named published conjectures:"
    printf '    %s\n' "${CLASSIFIED_CITATIONS[@]}"
    echo ""
    echo "  Each is a Category B axiom declared in this script's axiom contract."
    echo "  A theorem listed here is not kernel-only; it is a reduction to the"
    echo "  named citation. Theorems not listed carry only the kernel three."
  else
    echo ""
    echo "  No citation axioms appeared: every inspected theorem is kernel-only."
  fi
  echo ""
  echo "  Build log:        ${BUILD_LOG}"
  echo "  Axiom check log:  ${AXIOM_LOG}"
  exit 0

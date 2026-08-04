# The canonical α-dictionary and ch₂-ladder (reconciliation table)

**Date: 2026-08-04.**
**Repair item P8** of the 2026-08-01 full-corpus audit
(`codex/CORPUS_FULL_READ_2026-08-01.md`).

The corpus states the α-skeleton and the ch₂-ladder in several places,
and the statements do not all agree. Per house rule, nothing is deleted:
this file is the single reconciliation table. It says which formula is
canonical and which occurrences are stale variants, with file + line
references for every occurrence found in README, docs, Papers, and the
book source.

**Honest status, first:** even the CANONICAL values below are *declared,
not derived*. The kernel proves algebraic identities among the declared
constants (the twelve invariants), and uniqueness modulo four declared
anchors (r128). It does not derive the constants from first principles.
The α_NP pin in particular is an empirical calibration
(`alphaNP_unconstrained`, kernel-verified). See `OPEN_PROBLEMS.md`.

---

## 1. The canonical α-dictionary (nine values)

| Axis | Canonical α | Notes |
|---|---|---|
| Poincaré (resolved) | 1 | Perelman 2003 anchor (declared input) |
| P | √2 ≈ 1.414 | |
| RH | 3/2 | |
| Hodge | φ = (1+√5)/2 ≈ 1.618 | |
| NP | φ + 1/4 ≈ 1.868 | calibration, not derivation |
| Yang–Mills | 2 | |
| BSD | 3π/4 ≈ 2.356 | |
| QG | √(2π) ≈ 2.507 | |
| Navier–Stokes | 3π/2 ≈ 4.712 | **NOT 5/3** |

### Canonical sources (consistent with the table above)

| Source | Location |
|---|---|
| Lean, r128 nine-tuple uniqueness | `PF_Lean4_Code/PF/AlphaSkeletonUniqueness_r128.lean` |
| Lean, invariants | `PF_Lean4_Code/PF/CrossMillenniumSharedInvariants.lean` |
| Skeleton paper | `Papers/principia_fractalis_alpha_skeleton_2026-07-13.tex` lines 241, 271 |
| README reference table | `README.md` §"The substrate's α-skeleton" (line ~206) |
| Referee quickstart §5 | `docs/REFEREE_QUICKSTART.md` lines ~185–210 |
| Book ch03 table (corrected 2026-05-18) | `Principia_Fractalis_master_folder/chapters/ch03_resonance.tex` lines 216–234 (`tab:resonance-values`) |

### Stale / conflicting variants (left in place; superseded by the table above)

| Variant | Location | What it says | Status |
|---|---|---|---|
| NS = 5/3 "Kolmogorov cascade" | `chapters/ch07_constants.tex` line 245 | table row gives α_NS = 5/3 | STALE — pre-2026-05-18 dictionary; canonical is 3π/2. The ch03 caption records the same old triple (NS = 5/3, BSD = φ+1/3, Hodge = π/2) as corrected |
| π attributed to NS, e to YM | `chapters/ch07_constants.tex` lines 243–244 | "Circle Constant π → navier-stokes", "Growth Constant e → yang-mills" | STALE chapter cross-refs; π and e are not axis values; e is not even in the canonical basis {1, π, φ, √2} |
| RH ↔ α = 1/2 | `chapters/ch01_numbers.tex` line 1366 | "α = 1/2: Connects to Riemann Hypothesis" | STALE/WRONG — conflates the critical line Re(s) = 1/2 with the α-value; canonical α_RH = 3/2 |
| YM ↔ α = e | `chapters/ch01_numbers.tex` line 1368 | "α = e: Connects to Yang-Mills" | STALE — canonical α_YM = 2 |
| α_NP = π/3 in code | `chapters/ch34_verification.tex` lines 228–230; `chapters/ch35_software.tex` line 338 | Protocol P1 code uses `alpha=np.pi/3` for H_NP | CONFLICTING — π/3 ≈ 1.047 ≠ φ + 1/4 ≈ 1.868. Already disclosed in the ch34 honest-scope note (line 184) and ledger (line 794): "either way it is a chosen value, not a derived one" |

---

## 2. The ch₂-ladder (consciousness-threshold ladder)

The corpus contains **two incompatible ladder formulas** plus at least
four further operationalizations of ch₂ = 0.95 = c₂ = 19/20. None of
them is derived; c₂ itself is a phenomenological anchor whose four
attempted derivations are refuted or downgraded (see the v2 paper's
honest-scope section and the ch11 ledger).

### Variant A — baseline 3/2 (majority usage; treat as the corpus's working form)

    ch₂(axis) = 0.95 + (α_axis − 3/2) / 10

| Occurrence | Location |
|---|---|
| YM: 0.95 + (2 − 3/2)/10 = 1.00 | `chapters/ch23_yang_mills.tex` line 528 |
| BSD: 0.95 + (3π/4 − 3/2)/10 ≈ 1.0356 | `chapters/ch24_birch_swinnerton_dyer.tex` lines 538, 545 ("Riemann (α = 3/2): ch₂ = 0.95 (baseline)") |
| Hodge: 0.95 + (φ − 3/2)/10 ≈ 0.9618 | `chapters/ch25_hodge_conjecture.tex` lines 486–487 |

### Variant B — baseline √2 (ch21 only; incompatible with Variant A)

    ch₂(class) = 0.95 + (α_class − √2) / 10

| Occurrence | Location |
|---|---|
| P: 0.95 + (√2 − √2)/10 = 0.95 | `chapters/ch21_p_vs_np.tex` line 1164 |
| NP: 0.95 + ((φ+1/4) − √2)/10 ≈ 0.9954 | `chapters/ch21_p_vs_np.tex` line 1169 |

**The conflict, precisely:** Variant A pins ch₂ = 0.95 at the RH axis
(α = 3/2); Variant B pins ch₂ = 0.95 at the P class (α = √2). One
ladder cannot do both. Under Variant A, ch₂(P) would be ≈ 0.9414, not
0.95. No occurrence derives its baseline; both are calibrated so that
a chosen axis sits exactly at the 0.95 threshold.

**Ruling (2026-08-04):** neither variant is canonical as mathematics —
both are asserted calibrations. Where a single working form is needed
for internal consistency, Variant A (baseline 3/2) is the majority form
and is what ch23/ch24/ch25 already use; ch21's Variant B stands as a
documented divergent variant. Do not cite either ladder as a derived
result.

### Other ch₂ = 0.95 operationalizations (not ladder formulas; listed for completeness)

| Operationalization | Location | Status |
|---|---|---|
| 14D trace anomaly: ch₂ = (4π)⁷⟨ΔΦ⟩/(A₁₄⟨R²⟩) = 0.95 ± 0.01 | `chapters/ch11_geometric_unity.tex` lines 143, 168 | REFUTED — machine-checked `anomaly_cancel_predicted_value_ne_0_95` (off by ~1570×) |
| Gaussian integral: ⟨\|Ψ_RQG\|²⟩ = √(5/(π+5)) ≈ 0.7837 claimed ≈ 0.95 | `chapters/ch11_geometric_unity.tex` line 199 | REFUTED — machine-checked `prop_11_6_psi_rqg_sq_ne_0_95` (0.7837 ≠ 0.95) |
| Entropy form: ch₂(ℰ) = 0.95 + (H/H_max)·0.05 | `chapters/ch22_navier_stokes.tex` line 404 | asserted; a third, distinct functional form (range [0.95, 1.00]) |
| Percolation form: σ_c = 6/π² + ε_quantum = 0.95 | `chapters/ch25_hodge_conjecture.tex` line 302 | asserted; ε_quantum ≈ 0.3421 is chosen to hit 0.95 |
| appH scale: ch₂ = 0.5 (normal) / 0.95 (threshold) / 1.2 (Omega) | `Principia_Fractalis_master_folder/appendices/appH_numerical_validation.tex` lines 203–215 | a fifth scale; note ladder Variant A already produces values > 1 (BSD ≈ 1.0356), so "ch₂ ≤ 1 as a probability-like threshold" and the ladder cannot both hold |

---

## 3. Rule going forward

- New text cites the §1 canonical table and names it "declared".
- Any ch₂ number must name which variant (A / B / other) produced it.
- Stale variants above are NOT to be silently edited; if one is
  corrected in place, the correction must be dated and additive, per
  the house style (r182 pattern).

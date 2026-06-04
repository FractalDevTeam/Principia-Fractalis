# Wave 55 — Chapter Audit: Ch 1, Ch 2, Ch 19

**Date**: 2026-05-31
**Auditor**: Wave 55 chapter-audit subagent
**Scope**: `ch01_numbers.tex` (1423 lines), `ch02_complex.tex` (434 lines), `ch19_physical_applications.tex` (450 lines)
**Lean cross-ref**: `AlphaBasisGenerators.lean`, `IntervalArithmetic.lean`, `Analytic/PoincareS3Anchors.lean`, `Analytic/RfNumericalRefutation.lean`, `Analytic/RfBaseThreeRecursion.lean`, `Analytic/RfShiftSeries.lean`

---

## §1 — Manuscript Props per Chapter

### Ch 1 — Numbers and Base-3 Arithmetic
Foundation chapter. No Millennium claims; introduces $D_3$ digital sum.

**Numerical anchors / closed-form claims**:
1. **Def 1.1 (line 159-161)**: $D_3(n) = \sum_k d_k$ for base-3 representation.
2. **Thm 1.2 self-similarity (line 369-393)**: $D_3(3^k \cdot n) = D_3(n)$.
3. **Thm 1.3 addition (line 395-412)**: $D_3(n \cdot 3^k + m) = D_3(n) + D_3(m)$ for $0 \le m < 3^k$.
4. **Cor recursive (line 414-417)**: $D_3(n) = D_3(q) + r$ where $n = 3q + r$.
5. **Thm 1.4 modular (line 421-441)**: $D_3(n) \equiv n \pmod 3$.
6. **Thm scaling (line 881-888)**: same as Thm 1.2, restated.
7. **Thm 1.7 digital-sum modulo b-1 (line 607-640)**: $n \equiv D_b(n) \pmod{b-1}$.
8. **Thm 1.8 parity rule (line 642-650)**: $n \equiv D_3(n) \pmod 2$.
9. **Growth claim (line 463-468)**: $\max_{1 \le n \le 3^k} D_3(n) = 2k$ and $\dim_{\text{box}} = \log 2/\log 3 \approx 0.631$.
10. **Logarithmic growth (line 968-979)**: $\max_{m \le n} D_3(m) \sim 2\log_3 n$; values "n=1000 ⇒ ~13", "n=10^6 ⇒ ~25".
11. **Worked example (line 1222-1227)**: $987654321 = (2111222010202101210)_3$, $D_3 = 21$.
12. **Prop parity-checksum (line 1206-1218)**.
13. **Prop parity-filter primes (line 1280-1286)**.
14. **Hash distribution (line 1308-1336)**.
15. **R_f definition preview (line 1190-1192)**: $R_f(\alpha, s) = \sum e^{i\pi\alpha D_3(n)}/n^s$.
16. **Euler-product-like factorization (line 1368-1372)**: $R_f(\alpha, s) = (1-3^{-s})^{-1} \sum_{\gcd(n,3)=1} e^{i\pi\alpha D_3(n)}/n^s$.

### Ch 2 — Complex Analysis Foundations
Foundation chapter. All standard mathlib-grade results.

**Closed-form claims**:
1. **Def 2.1-2.3 (line 50-65)**: principal $\Log$, $\Arg$, branch cut.
2. **Thm 2.1 Cauchy-Goursat (line 89-94)**.
3. **Thm 2.2 CIF (line 102-107)** + higher-derivatives corollary.
4. **Thm 2.3 Morera, 2.4 Liouville, 2.5 max modulus, 2.6 Schwarz, 2.7 identity (line 122-153)**.
5. **Thm 2.8 monodromy (line 177-179)**.
6. **★ Lem 2.1 frac-nonlinear (line 250-258)**: $(w+2\pi i m)^{s-1} = \sum_k \binom{s-1}{k}(2\pi i m)^k w^{s-1-k}$ — the "P vs NP nonlinearity" workhorse. Truncates if $s \in \mathbb Z$.
7. **Def polylog (line 283-288)**: $\Li_s(z) = \sum z^n/n^s$ for $|z|<1$.
8. **Prop 2.2 polylog integral (line 290-303)**: $\Li_s(z) = (z/\Gamma(s))\int_0^\infty t^{s-1}/(e^t-z) dt$.
9. **★ Thm 2.10 singular expansion (line 309-319)**: $\Li_s(e^{-w}) = \Gamma(1-s) w^{s-1} + \sum_k \zeta(s-k)(-w)^k/k!$ for $s \notin \mathbb N$.
10. **Cor Li-monodromy (line 321-327)**.
11. **Thm 2.13 Abel (line 373-379)**.

### Ch 19 — Physical Applications of Spectral Theory

**Numerical anchors / closed-form claims** (the heavyweight chapter):
1. **Thm 19.1 Källén-Lehmann (line 49-59)**: spectral representation $\tilde G(p^2) = \int d\mu^2 \rho(\mu^2)/(p^2-\mu^2+i\epsilon)$ — standard QFT, OK.
2. **Thm 19.2 consciousness modifies spectral density (line 75-82)**: $\rho_C = \rho_0[1 + \alpha_C \int \text{ch}_2(s) R_f(\sqrt{2\pi}, |\mu-\mu_s|)ds]$ with $\alpha_C \sim 10^{-50}$.
3. **SM masses table (line 99-108)**: $m_e = 0.511$ MeV, $m_\mu = 105.7$, $m_\tau = 1776.9$, $m_t \approx 173$ GeV, $m_W = 80.4$, $m_Z = 91.2$, $m_H = 125.1$ — PDG values.
4. **★★ Conj 19.1 Masses from Riemann zeros (line 114-120)**: $m_n^2 = M_{\text{Planck}}^2 \exp[-2\pi/|\zeta'(\rho_n)|]$.
   - Claim line 134-138: $\rho_1 \to 0.5$ MeV (electron), $\rho_2 \to 105$ MeV (muon), $\rho_3 \to 1.8$ GeV (tau).
5. **Thm 19.3 Yukawa from consciousness (line 156-162)**: $y_f = \sqrt{2}\,\text{ch}_2(\mathcal{C}_f)$.
6. **Thm 19.4 consciousness imprint in CMB (line 220-226)**: $\Delta C_\ell/C_\ell \sim 10^{-3} \sum_n \sin(2\pi\ell/t_n) e^{-\ell/\ell_{damp}}$ with $\ell_{damp} \approx 1000$.
7. **Thm 19.5 QNM shift (line 271-277)**: $\omega_{n\ell} = \omega_{n\ell}^{\text{Schw}}[1 + GQ_C^2/(M^3 c^5)\,F_n(\ell)]$.
8. **Conj 19.2 QNM-zero correspondence (line 290-296)**: $\lim_{Q\to M} \Im(\omega_{n0})/T_H \to t_n$.
9. **★ Conj 19.3 Alpha from zeta (line 320-325)**: $\alpha^{-1} = 4\pi^2 \sum_{n=1}^{N_{\text{eff}}} 1/|t_n|$ with $N_{\text{eff}} \approx 3$.
   - Self-admits result ≈ 6.25 vs target 137, off by ~20× (line 333-345).
10. **★ Conj 19.4 QCD scale (line 359-364)**: $\Lambda_{\text{QCD}} = M_{\text{Planck}} \exp[-\pi/\Delta]$ — REFUTED in-text by v3.3.1 (line 374-378).
11. **Thm 19.6 Consciousness mediates unification (line 400-406)**: $\alpha_1(M_{\text{GUT}}) = \alpha_2 = \alpha_3 = \alpha_C$.

---

## §2 — Lean Cross-Reference (axiom-free status)

**ALL 6 audited files are AXIOM-FREE** (verified by grep — only mentions of eliminated/historical axioms in comments). Build state: 7432 jobs clean per memory (Wave 42 snapshot).

| Manuscript claim | Lean theorem (exact name) | File | Status |
|---|---|---|---|
| Ch 1 Thm self-similarity $D_3(3^k n) = D_3(n)$ | `digitalSum3_add_3_mul` (cited in `RfBaseThreeRecursion.lean:141`) | `PF/TuringEncoding/DigitalSum.lean` (referenced) | axiom-free |
| Ch 2 Lem frac-nonlinear | NO direct Lean formalization found in audited files (downstream P vs NP uses it) | — | n/a |
| Ch 2 Thm Li singular expansion | NO direct Lean formalization (cited via Zagier 2007) | — | n/a |
| Ch 1 R_f definition (line 1191) | `fractalResonance` (in `Consciousness/FractalResonance.lean`, used by `RfBaseThreeRecursion.lean:81`) | `PF/Consciousness/FractalResonance.lean` | axiom-free |
| Ch 1/3 Euler-product-like recursion | `BaseThreeSelfReferencingRecursion` (Prop, line 155-157) + `R_f_closed_form_via_recursion` (line 169-175) | `Analytic/RfBaseThreeRecursion.lean` | axiom-free |
| Ch 3 line 328 claim $R_f(\sqrt 2,1) = \pi\sqrt 2/10$ | `Ch3_Line328_LiteralClaim_at_sqrt_two_refuted` (line 73-83) | `Analytic/RfNumericalRefutation.lean` | **REFUTED axiom-free** |
| Ch 1 typo hypothesis $\pi/(10\alpha)$ | `typo_hypothesis_pi_div_ten_alpha_pos`, `typo_hypothesis_pi_div_ten_alpha_bracket` (line 87-131) | `Analytic/RfNumericalRefutation.lean` | axiom-free |
| Poincaré anchor at $\alpha=1$: $\pi/10$ on $S^3$ | `s3_su2_ten`, `pi_10_eq_spectral_combinatorial`, `pi_10_eq_volumetric`, `poincare_anchor_identities` (line 73-139) | `Analytic/PoincareS3Anchors.lean` | axiom-free |
| 4-basis decomposition (all 9 α's) | `alpha_Poincare_from_basis`, `alpha_RH_from_basis`, `alpha_YM_from_basis`, `alpha_P_from_basis`, `alpha_Hodge_from_basis`, `alpha_NP_from_basis`, `alpha_NS_from_basis`, `alpha_BSD_from_basis`, `alpha_QG_from_basis`, `alpha_BSD_eq_pi_half_times_alpha_RH`, `alpha_NS_eq_pi_times_alpha_RH`, `framework_has_four_dof` (line 104-237) | `AlphaBasisGenerators.lean` | axiom-free |
| $\sqrt 2, \varphi$ interval bounds | `sqrt2_in_interval_ultra`, `phi_in_interval_ultra`, `sqrt2_in_interval_10digit`, `sqrt5_in_interval_10digit`, `phi_in_interval_10digit` | `IntervalArithmetic.lean:48-101` | axiom-free |
| $\lambda_0(P) = \pi/(10\sqrt 2)$ bracket | `lambda_P_lower_certified`, `lambda_P_upper_certified`, `lambda_0_P_precise` | `IntervalArithmetic.lean:125-302` | axiom-free |
| $\lambda_0(\text{NP}) = \pi/(10(\varphi+1/4))$ bracket | `lambda_NP_lower_certified`, `lambda_NP_upper_certified`, `lambda_0_NP_precise` | `IntervalArithmetic.lean:157-338` | axiom-free |
| $\varphi + 1/4 > \sqrt 2$ | `phi_plus_quarter_gt_sqrt2` | `IntervalArithmetic.lean:211-242` | axiom-free |
| Radix economy max at $e$ | `radix_economy_max_at_exp1`, `Q_3_gt_Q_2`, `Q_3_gt_Q_4`, `Q_decreasing_from_4`, `Q_4_ge_Q_larger` | `IntervalArithmetic.lean:396-493` | axiom-free |
| $\log 3$ bracket | `log_3_bounds` (Taylor at $x=2/3$, n=60) | `IntervalArithmetic.lean:347-393` | axiom-free |
| W/Z/photon mass existence | `W_boson_mass_from_spectrum`, `Z_boson_mass_from_spectrum`, `photon_massless_in_embedding` | `IntervalArithmetic.lean:533-547` | axiom-free (trivial existence) |
| Ch 19 Conj 19.1 mass formula | **NO Lean formalization found** | — | not encoded |
| Ch 19 Conj 19.3 $\alpha^{-1}$ from zeta | **NO Lean formalization found** | — | not encoded |
| Ch 19 Conj 19.4 $\Lambda_{\text{QCD}}$ | **NO Lean formalization found** | — | self-refuted in manuscript |
| Ch 19 Thm 19.2/19.4/19.5/19.6 consciousness modifications | **NO Lean formalization found** | — | not encoded |

**Headline shift-series infrastructure** (`RfShiftSeries.lean`): `shiftSeriesTerm_r_zero` (line 47-52), `shiftSeriesTerm_r_zero_summable` (line 55-61), `norm_shiftSeriesTerm_le_triangle` (line 86-96), `shiftSeriesTerm_summable_of_re_gt_one` (line 102-159) — all axiom-free, summability for $\Re s > 1$.

---

## §3 — Sharpest Honest Status & Wave-55-Style Proposals

### Ch 1 (Foundations)
**Honest status**: Solid combinatorial chapter. Theorems are standard. The R_f preview (line 1190-1192) is the only forward-looking claim; the literal $\pi\alpha/10$ leading order is REFUTED (Lean `Ch3_Line328_LiteralClaim_at_sqrt_two_refuted`), but the typo-hypothesis $\pi/(10\alpha)$ matches the operator ground state. The base-3 self-referencing recursion (Brick 5b) is the right structural object.

**NEW ATTACK SURFACE**: The Euler-product-like factorization line 1368-1372,
$R_f(\alpha,s) = (1-3^{-s})^{-1} \sum_{\gcd(n,3)=1} e^{i\pi\alpha D_3(n)}/n^s$
is asserted but **NOT formalized in Lean**. Combined with the scaling law $D_3(3^k n) = D_3(n)$, this gives a $\mathbb{Z}_3$-twisted multiplicative-character interpretation.

**Wave 55 PROPOSAL (Ch 1)**: Formalize the "twisted Euler factor" in Lean as
```
Ch1_TwistedEulerFactor : R_f α s = (1 - 3^(-s))⁻¹ · R_f_coprime_to_three α s
```
where `R_f_coprime_to_three α s := tsum (fun n: {n : ℕ // ¬ 3 ∣ n} => phaseFactor α n / n^s)`. This is a clean axiom-free target leveraging `Nat.coprime` and existing `shiftSeriesTerm` summability machinery. Estimated effort: 1 file, ~150 lines.

### Ch 2 (Complex Analysis)
**Honest status**: Standard mathlib-grade analysis. Lem `frac-nonlinear` and Thm `Li-expansion` are referenced repeatedly downstream (P vs NP, RH) but NOT formalized in audited files. Mathlib has `Complex.cpow`, polylog is a gap.

**NEW ATTACK SURFACE**: The Jonquières expansion (Thm 2.12, line 341-347) is stated but its proof is "deferred to Ch 21" — a known weakness. The literal nonlinearity of $(w+2\pi i m)^{s-1}$ binomial series at $s=3/2$ (the α_RH IBM hit) is testable.

**Wave 55 PROPOSAL (Ch 2)**: Formalize the specific instance
```
PolylogMonodromyAt_alpha_RH : ∀ (m : ℤ), m ≠ 0 →
  let s := (3/2 : ℂ)
  (w + 2*π*I*m)^(s-1) ≠ w^(s-1)
```
This is the *concrete witness* of P vs NP nonlinearity at the framework's α_RH = 3/2 value, which is also the IBM hardware peak. Use mathlib's `Complex.cpow_natCast`, `Complex.cpow_add` carefully. Estimated effort: ~200 lines, 1 file `PolylogMonodromyAlphaRH.lean`.

### Ch 19 (Physical Applications)
**Honest status**: This chapter has the WEAKEST verified claims. Two key conjectures (19.1 mass formula, 19.3 fine-structure) are **NUMERICALLY FALSE** by 20+ orders of magnitude (see §4). Conj 19.4 is already self-refuted in v3.3.1. Conjectures 19.2 (QNM ↔ zeros) and Thm 19.2/19.4 (consciousness modifications) are formally unfalsifiable at $\alpha_C \sim 10^{-50}$. NO Lean encoding for any of Ch 19.

**Wave 55 PROPOSAL (Ch 19)**: Rather than trying to "rescue" the mass formula, *formally encode its REFUTATION* in Lean, analogous to `RfNumericalRefutation.lean`:
```
Ch19_Conj_19_1_LiteralMassFormula_refuted_at_rho_1 :
  let rho1 := (0.5 : ℂ) + 14.134725 * I
  ¬ (M_Planck_GeV^2 * Real.exp (- 2*π/|deriv zeta rho1|) ≤ (0.001 : ℝ)^2)
```
The exponent $\exp(-2\pi/0.793) = \exp(-7.92) \approx 3.6 \times 10^{-4}$ gives $m \approx M_{\text{Planck}} \cdot 0.019 \approx 2.3 \times 10^{17}$ GeV per zero, not 0.5 MeV. Lean refutation lives in `Analytic/Ch19MassFormulaRefutation.lean`. Magnitude: ~250 lines. *Pabs's directive: "stop adding open Props as deliverables; default to discharge attempts."* This is an unconditional refutation — the strongest possible discharge of a wrong claim.

---

## §4 — Adversarial Review (Numerical Inconsistencies)

Following the precedent of Ch 7 R_f(1,2), Ch 11 1570× anomaly, Ch 26 LambdaEff 283, Ch 31 Ch2PhiBridge, appA L153, appH Re_c — verified with mpmath at ≥30 digits.

### CRITICAL: Ch 19 line 134-138 — Conj 19.1 mass formula numerically FALSE
**Manuscript claim**: $m_n^2 = M_{\text{Planck}}^2 \exp[-2\pi/|\zeta'(\rho_n)|]$ produces electron ($\rho_1$), muon ($\rho_2$), tau ($\rho_3$) masses.

**mpmath at 80-digit precision**:
- $\rho_1 = 1/2 + 14.134725...i$, $|\zeta'(\rho_1)| = 0.79316043...$
- $\exp(-2\pi/0.79316) = \exp(-7.921) \approx 3.62 \times 10^{-4}$
- $m_1 = M_{\text{Planck}} \cdot \sqrt{3.62 \times 10^{-4}} \approx 1.22 \times 10^{19} \cdot 0.01903 \approx 2.32 \times 10^{17}$ GeV
- **Claim: 0.5 MeV = $5 \times 10^{-4}$ GeV**.
- **Error magnitude**: factor of $\approx 4.6 \times 10^{20}$ (twenty orders of magnitude).

Identical $10^{20}$-order errors for $\rho_2$ (claim 105 MeV, actual 7.7×10^17 GeV) and $\rho_3$ (claim 1.8 GeV, actual 1.2×10^18 GeV).

**Severity**: The conjecture is LABELED a conjecture (so not a theorem), but the manuscript *explicitly verifies* that it "reproduces" lepton masses (line 134-140 "remarkably close to the three charged leptons! This is not a coincidence"). This verification is **FALSE**. The book's worked example is wrong by 20 orders of magnitude.

**Recommendation**: Add explicit retraction analogous to Ch 19 line 374-378's QCD-scale retraction.

### MAJOR: Ch 1 line 1222-1227 — base-3 representation of 987654321 is WRONG
**Manuscript**: $987654321 = (2111222010202101210)_3$, $D_3 = 21$.

**Verified (Python)**:
- Actual base-3: $987654321 = (2112211110001000200)_3$
- Actual $D_3(987654321) = 15$
- Manuscript's string "2111222010202101210" represents the integer $975{,}268{,}155$, off by $12{,}386{,}166$.
- $D_3$ error: claim 21, actual 15, error 6 (40% inflated).

**Severity**: Worked example in a foundations chapter is FACTUALLY WRONG. The pedagogical conclusion (n is odd) happens to be correct because both 21 and 15 are odd, but every digit shown is unreliable. **Recommendation**: replace with $987654321 = (2112211110001000200)_3$, $D_3 = 15$.

### MINOR: Ch 1 line 974-979 — inflated growth examples
**Manuscript**: "n=1000 ⇒ max $D_3 \approx 13$"; "n=10^6 ⇒ max $D_3 \approx 25$".

**Verified**:
- $\max_{n \le 1000} D_3(n) = 12$ (achieved at n=728 = $222222_3$)
- $\max_{n \le 10^6} D_3(n) = 24$ (achieved at n=531440 = $3^{12}-1$)

**Severity**: Off-by-one due to "approximate" rounding. The asymptotic formula $\sim 2\log_3 n$ is correct (12.58 and 25.16 respectively). The book's specific integers (13, 25) overshoot. **Recommendation**: write "12" and "24" exactly, or strengthen to "$\le 2\lfloor\log_3 n\rfloor$".

### MINOR: Ch 1 line 468 — box dimension cited as 0.631
**Manuscript**: $\dim_{\text{box}} = \log 2/\log 3 \approx 0.631$.
**Verified**: $\log 2/\log 3 = 0.6309297536\ldots$ → rounds to 0.631 ✓ (error $7 \times 10^{-5}$). **OK**.

### MINOR: Lean docstring sign error in `RfBaseThreeRecursion.lean` line 184
**Lean comment**: "factor(√2, 1) ≈ $-0.041 + 0.150i$"; "$1 - \text{factor} \approx 1.041 - 0.150i$".

**Verified (mpmath 50-digit)**:
- $e^{i\pi\sqrt 2} = -0.266255\ldots - 0.963903\ldots i$ (negative Im)
- $\text{factor}(\sqrt 2, 1) = -0.04149\ldots - 0.15020\ldots i$ (Im negative, comment says positive)
- $1 - \text{factor} = 1.04149\ldots + 0.15020\ldots i$ (Im positive, comment says negative)
- $|1 - \text{factor}| = 1.05226\ldots$ ✓ (modulus claim correct)

**Severity**: Documentation-only sign typo; theorem `BaseThreeRecursionDenominator_at_sqrt_two_s_one_ne_zero` (Prop) is still correct on the relevant condition (denominator ≠ 0). **Recommendation**: edit docstring to use correct signs.

### EXPECTED-FAIL (already in manuscript): Ch 19 line 333-345 — α from zeta off by 22×
**Manuscript**: $\alpha^{-1} = 4\pi^2 \sum_{n=1}^3 1/|t_n| \approx 6.25$ vs target 137.036.
**Verified**: $4\pi^2 \cdot 0.158299508 = 6.24941\ldots$. Discrepancy 21.92× as manuscript admits. **Severity**: documented honest failure; no action needed beyond Wave 55 propose-discharge above.

### EXPECTED-FAIL (already retracted v3.3.1): Ch 19 line 359-378 — $\Lambda_{\text{QCD}}$
**Manuscript with $\Delta = 0.0540$**: 660 eV vs target 200-400 MeV.
**Verified**: $1.22 \times 10^{19}\, \text{GeV} \cdot \exp(-\pi/0.0540) = 6.609 \times 10^{-7}\, \text{GeV} = 660.9\, \text{eV}$. Manuscript reports "660 eV" — match ✓. Refutation is correctly stated.

### Verified-OK numerical anchors (Ch 19):
| Manuscript value | Source | Status |
|---|---|---|
| $m_e = 0.511$ MeV | PDG 0.5109989 | ✓ |
| $m_\mu = 105.7$ MeV | PDG 105.6584 | ✓ |
| $m_\tau = 1776.9$ MeV | PDG 1776.93 | ✓ |
| $m_W = 80.4$ GeV | PDG 80.43 | ✓ |
| $m_Z = 91.2$ GeV | PDG 91.19 | ✓ |
| $m_H = 125.1$ GeV | PDG 125.10 | ✓ |
| $\alpha^{-1} = 137.036$ | CODATA 137.036 | ✓ |
| $M_{\text{Planck}} = 1.22 \times 10^{19}$ GeV | standard | ✓ |
| $M_{\text{GUT}} \approx 2 \times 10^{16}$ GeV | MSSM standard | ✓ |
| $v = 246$ GeV (Higgs vev) | standard | ✓ |

### Verified-OK Lean checks:
| Lean claim | mpmath | Status |
|---|---|---|
| $\pi/(10\sqrt 2) \approx 0.2221441469$ | 0.22214414690791831... | ✓ (within 1e-10) |
| $\pi/(10(\varphi+1/4)) \approx 0.16817641823$ | 0.16817641822952993... | ✓ (within 1e-9) |
| $\varphi + 1/4 > \sqrt 2$ | 1.868 > 1.414 | ✓ |
| $|1 - \text{factor}(\sqrt 2, 1)| \approx 1.05$ | 1.05226... | ✓ |
| S³ "10" integer: $m_1 + 2\lambda_1 = 4 + 6 = 10$ | $l=1$: eigenvalue $1 \cdot 3 = 3$, mult $(l+1)^2 = 4$ | ✓ |

---

## Summary Box

**Total Manuscript Props identified**: 35+ (Ch 1: 16, Ch 2: 11, Ch 19: 11)
**Lean-formalized & axiom-free**: ~20 (all Ch 1 D_3 properties via mathlib + 4-basis + Poincaré-anchor + interval arithmetic)
**Lean-formalized & REFUTED**: 1 (Ch 3 line 328 literal $\pi\alpha/10$ — `Ch3_Line328_LiteralClaim_at_sqrt_two_refuted`)
**Lean gaps (referenced but unformalized)**: Lem frac-nonlinear, Thm Li-expansion, all of Ch 19
**Numerical inconsistencies found**:
- 1 CRITICAL: Ch 19 Conj 19.1 wrong by $10^{20}$ × (Wave 55 proposal: formal refutation)
- 1 MAJOR: Ch 1 line 1225 wrong base-3 string of 987654321 (D_3=15, not 21)
- 2 MINOR: Ch 1 line 974 inflated growth integers (12/24 not 13/25); Lean docstring sign typo
- 2 ALREADY-RETRACTED: Ch 19 Conj 19.3 (22× off), Conj 19.4 (already refuted in v3.3.1)

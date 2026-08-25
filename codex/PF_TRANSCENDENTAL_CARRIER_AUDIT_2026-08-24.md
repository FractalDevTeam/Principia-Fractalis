# PRINCIPIA FRACTALIS — TRANSCENDENTAL CARRIER AUDIT

**Date:** 2026-08-24
**HEAD:** `47f990d74af39ce567684590b292f2a8aeffcb3a` (r320 on origin/master)
**Companions:** `codex/ALPHA_SKELETON_INTRINSIC_ORIGIN_AUDIT_2026-08-24.md`, `codex/ALPHA_SKELETON_STRUCTURAL_LAW_PROVENANCE_2026-08-24.md`
**Deliverable:** the READ-ONLY transcendental-carrier audit mandated by the post-r320 directive.

> **POST r220/r222 AUDIT RECONCILIATION — 2026-08-24 (same day, later).**
>
> The class-B candidate recommended in §13 below (the r222 ω-inversion,
> `logFrequency_characterized_by_sqrt3_shift`) is **REVOKED**. A focused
> semantic audit of r220 and r222 (`codex/R220_R222_LOG_FREQUENCY_ORIGIN_AUDIT_2026-08-24.md`)
> established that the premise "√3-adjacent-zero shift" is not independently
> derived; it is a downstream consequence of the same definitional
> `logFrequency := 2π / log 3` the theorem was proposed to characterize.
> The proposed theorem is a definitional restatement dressed as a
> characterization, not a genuine class-B result.
>
> **Corrected count:** 0 class-A π-generators formalized; 0 class-B
> π-characterizations formalized; **0 known tractable class-B candidates**
> (previously stated as "1 tractable class-B candidate — retracted).
>
> The rest of this audit's factual content is unchanged — the survey,
> the absences, the classification distribution. Only the recommendation
> in §13 is retracted. The status locked into subsequent research is
> the one recorded in the r220/r222 companion audit's §11.

The central question this document answers:

> **Does Principia Fractalis already contain an α-independent canonical object from which π emerges as a theorem output rather than as a definitional input?**

Not "where does `Real.pi` occur." That is too weak — π appears throughout ordinary mathematics. The question is whether π is **generated** or **selected** by a PF object whose definition does not already contain π or an equivalent encoding.

The prior structural-law provenance audit identified L5 (`α_NS = α_RH · π`) as the sole load-bearing narrative gap in the eight r128 structural laws. r320 (`memZ13_ratio_ne_pi`) formally ruled out the "ratio of two `ℤ[1/3]` trace-range values" route for L5's π-factor. This audit asks whether **any other** canonical PF construction supplies π.

---

## 1. HEAD

`47f990d74af39ce567684590b292f2a8aeffcb3a`

## 2. Corpus scope

- Total `.lean` files under `PF_Lean4_Code/PF/`: **1409** (per Explore agent count)
- Files containing `Real.pi`: **364** (~26%)
- Total direct `Real.pi` occurrences: **4761**
- Total `π` notation occurrences: **7997**
- Definitions with `Real.pi` on the RHS: **~53**

Two parallel Explore agents surveyed the corpus for (i) every π occurrence traced backward to its definition, and (ii) every canonical operator / dynamical / modular / crossed-product / nontracial structure.

## 3. Classification scheme

| Code | Meaning |
|---|---|
| **A** | Emergent / intrinsic: π-free PF object `O` has a theorem `invariant(O) = π`, forcing π uniquely. |
| **B** | Characterization: `O` (π-free in definition) satisfies a property whose unique positive solution is π-valued. |
| **C** | External classical structure: π comes from standard mathematics already in mathlib (circle geometry, `Real.exp` periodicity, Fourier theory), cited legitimately but not derived from PF substrate. |
| **D** | Normalization convention: π enters via a chosen Fourier / Mellin / theta convention. |
| **E** | Definition-injected: `Real.pi` appears literally in a PF `def` before any theorem is stated. |
| **F** | α-injected: π appears only after substituting a predefined α-value or α-law. |
| **G** | Target-encoded / circular: object chosen precisely so its solution / spectrum contains π. |
| **H** | Non-selective: construction yields arbitrary scale / period; π is one choice among many. |

The DIRECTIVE Part XI guardrail is explicit: "`Real.pi` inside a definition: NOT generation. Known theorem about circles: external classical input." Only classes A and B are structurally interesting. Class B is nearly as valuable as A.

## 4. Distribution of π occurrences by class

Combining the two Explore reports:

| Class | Approx count | Representative examples |
|---|---:|---|
| **A** — emergent | **0** | none found |
| **B** — characterization | **0** in the corpus as-currently-written; **1 tractable candidate** (see §7) |
| **C** — external classical | ~560 | `Real.pi_pos`, `Real.pi_gt_d2`, `Real.pi_lt_d4`, `Real.cos_pi_div_five`, `Real.sin_sq_add_cos_sq`, `MeasureTheory.integral_gaussian` |
| **D** — normalization convention | ~10 | `logFrequency := 2π / log 3` (r220), Xi/theta half-plane conventions, Fourier mode factors |
| **E** — definition-injected | ~53 | `α_NS := 3π/2`, `α_BSD := 3π/4`, `α_QG := √(2π)`, `lambda0 α := π / (10α)`, `sigma α := log₃ ‖1 + 2 cos(π α)‖`, `modular_FD_area := π/3` |
| **F** — α-injected | (subset of E) | `lambda0(α)`, `sigma(α)` evaluated at canonical α — π and α co-occur |
| **G** — target-encoded | 0 | none identified as pure G (some E's are F-flavored, chosen to hit α-encoded values) |
| **H** — non-selective | ~1 | `logFrequency` is base-3-specific; not "arbitrary scale" but is `2π / log(base)` with `base` a substrate constant, so more class-D-like than H |

**Class-A count: 0. Class-B count in current corpus: 0.**

## 5. What the corpus explicitly does not contain

Both Explore reports confirm the following absences:

| Absent structure | Consequence |
|---|---|
| **Fourier-transform machinery** (`Real.fourierIntegral`, `MeasureTheory.fourierIntegral`) used to prove self-duality | The DIRECTIVE Part VI's most-interesting-route (Gaussian self-duality forces `a = π`) has no infrastructure. Comments in `Analytic/CompletedZeta0Mellin*.lean` acknowledge classical θ/ξ self-duality but do not formalize it as a π-derivation. |
| **Gaussian self-duality theorem** (either BAD or GOOD pattern) | Neither `Fourier(exp(-π x²)) = exp(-π x²)` nor `Fourier(exp(-a x²)) = exp(-a x²) → a = π` appears in the corpus. |
| **KMS states** on `T_∞ = 3^∞` | r113's `substrate_UHF_trace_unique` forbids nontrivial tracial states; a KMS state at inverse temperature β ≠ 0 would induce a modular automorphism group and hence a distinct tracial state on the fixed-point subalgebra, contradiction. **No KMS enrichment path exists on the current substrate.** |
| **Crossed products** `T_∞ ⋊_α ℤ`, `T_∞ ⋊_α ℝ`, rotation algebras `A_θ` | Not defined anywhere in the corpus. A rotation algebra's K-theory `ℤ + θℤ` would inject irrational scale — but this exits the current substrate. |
| **Nontracial states / weights** | Not constructed. r113 uniqueness makes them impossible on `T_∞` itself. |
| **Explicit spectral computation** for `T3`, `T3_sym`, or any canonical operator | `TransferOperator.lean` proves self-adjointness, boundedness (`‖T3‖ ≤ 1`), formal-adjoint relation. **No eigenvalue is computed.** `T3SymContinuousSpectralMeasureAttempt.lean` acknowledges (lines 55-74) that the literal `T3_sym` has discrete spectrum and route-C reformulation is a substrate change. |
| **Base-3 dynamical invariants** (topological / measure entropy, Lyapunov, rotation numbers, pressure) | Not computed. Only period-2 fixed-point enumeration (r25) and `basethree_period2_fixed_points.card = 9`. |
| **Canonical geometric object** (manifold, sphere, torus) whose natural period intrinsically produces π from substrate data | Absent. `RHViaH3PerelmanBridge.lean` cites `sphere_S2_area = 4π` and `modular_FD_area = π/3` as **imported classical geometry**, not substrate-derived. |
| **Lindemann-Weierstrass transcendence machinery** | Mathlib has `irrational_pi`; no formal `Transcendental ℚ Real.pi` (r319 discovered this). Any richer transcendence obstruction is unavailable. |

## 6. Substrate oscillator — detailed status

The single non-trivial location where π occurs in a canonical α-independent PF context is the log-cosine ansatz machinery of r220 / r221 / r222 / r223.

**`PF/LogPeriodicity_r220.lean:270-274`**
```lean
noncomputable def logPeriod    : ℝ := Real.log 3
noncomputable def logFrequency : ℝ := 2 * π / Real.log 3
```

- `logPeriod` is π-free, α-free, canonical from the substrate base 3.
- `logFrequency` is DEFINITIONAL and contains π on the RHS. **Class E.**

**`PF/LogPeriodicity_r220.lean:285`**
```lean
theorem logFrequency_mul_logPeriod : logFrequency * logPeriod = 2 * π := by
  unfold logFrequency logPeriod; field_simp
```

- Unfolds the definition. Not a derivation.

**`PF/LogCosineNextZero_r222.lean:101-107`**
```lean
theorem logFrequency_log_sqrt_three_mul (x : ℝ) (hx : 0 < x) :
    logFrequency * Real.log (Real.sqrt 3 * x)
      = logFrequency * Real.log x + π := by
  have hkey : logFrequency * (logPeriod / 2) = π := by
    have := logFrequency_mul_logPeriod
    linarith
  ...
```

- The √3-next-zero shift derives from `logFrequency * (log 3 / 2) = π`, which is `logFrequency_mul_logPeriod / 2`, which reduces to the definition of `logFrequency` unfolded.
- **The √3 shift is downstream of the definitional insertion of π.** Class E → derived corollary.

**Nine `SubstrateOscillator` instances** (`PF/SubstrateOscillator_r223.lean:191-225`)

All nine take an input α and produce the ansatz `g(a) = A · a^σ(α) · cos(logFrequency · log a + φ₀)`. `σ(α)` and `logFrequency` are both π-containing (via definition). All nine are class E + F.

**`corpus_constant_amplitude_dichotomy`** (`r223:236`): proves exactly two of the nine (`α_Poincaré = 1`, `α_RH = 3/2`) have `σ = 0`. This is an F-class fact: it evaluates the α-dependent σ at the two rational canonical α's; π is not derived but the fact that these two α's are precisely the rational canonical values IS structurally informative — the substrate distinguishes them by giving trivial abscissa. Not a π-derivation, but a real substrate signature.

## 7. The single tractable class-B candidate

The r222 architecture contains — implicit in its statement structure — a legitimate class-B **inversion candidate**.

### The BAD pattern (currently present)

```
DEFINE logFrequency := 2π / log 3       (π-injected)
DEFINE g_{ω=logFrequency}(a) = A · a^σ · cos(ω · log a + φ₀)
PROVE  next-zero shift of g at √3 · a = next-zero shift at a    (√3 forced)
```

### The GOOD pattern (proposable as a NEW theorem)

```
DEFINE family g_ω(a) = A · a^σ · cos(ω · log a + φ₀)   -- ω : ℝ, FREE
DEFINE property "next-zero shift is √3 · a"            -- √3 = √(base 3), α-free, π-free
PROVE  ∀ ω > 0, (next-zero shift is √3 · a) → ω = 2π / log 3
                                                  -- ω uniquely characterized (class B)
```

The proof is elementary trigonometry:
- Setting `cos(ω · log a + φ₀) = 0` gives `ω · log a + φ₀ = (2k+1) π / 2` for some `k ∈ ℤ`.
- The next zero at `a' = c · a` (for `c > 1`) satisfies `ω · log(c · a) + φ₀ = (2k+3) π / 2`, i.e., `ω · log c = π`.
- Substituting `c = √3` gives `ω · (log 3) / 2 = π`, hence `ω = 2π / log 3`.
- **This is a genuine characterization**: the free positive parameter ω, given the canonical (α-free, π-free) `√(base)`-shift property, is forced to `2π / log 3`.

### Class assignment: **B (characterization)**, with a caveat

The DIRECTIVE Part XI is precise about the guardrail: "Gaussian self-duality with π already in Gaussian: tautological for our purposes." The analogous concern here: does the theorem's π on the RHS come from an external classical fact (period of `Real.cos` is `2π`) or from PF substrate?

- The `2` in `2π` is the coefficient in the period of `Real.cos`, external classical (mathlib).
- The `π` itself is `Real.pi`, external classical.
- The `log 3` is base-3-canonical, substrate-intrinsic.

**Honest labeling:** the theorem shows that in the canonical (base-3-shift, log-cosine ansatz) setting, the frequency ω is forced to be π-valued (specifically `2π / log 3`) by the periodicity of `Real.cos`. The π *origin* is external classical (`Real.cos` period), not PF substrate. The π *placement* — the specific value forced within the PF ansatz — is a genuine PF characterization.

So this candidate is **class B in the PF frame, class C in the absolute frame**. This is the DIRECTIVE's preferred pattern nonetheless: "This is nearly as valuable as A" (Part IV).

### Why the second Explore agent classified this as E

The auditor scanned for existing theorems. r222's current theorem uses `logFrequency` (defined with π) and derives the √3 shift, which is the BAD pattern. Inverting to the GOOD pattern is NOT currently in the corpus — it would be a new theorem. The auditor's finding "0 class-B candidates" is correct **as-of-current-corpus**; my finding "1 tractable class-B candidate" is a **proposed** addition, not an existing result.

## 8. Deliverable table — every candidate

Per DIRECTIVE Part VIII: for every candidate for a π-carrier, we tabulate:

| # | Object | File | π in def? | α in def? | Canonical? | Invariant computed? | Class | Arbitrary norm? | Current theorem | Exact missing theorem | Potential L5 connection |
|---|---|---|---|---|---|---|---|---|---|---|---|
| **T1** | `logFrequency` | `LogPeriodicity_r220.lean:274` | **YES** | no | yes (base-3) | `= 2π/log 3` by def | **E** | no (base-3 forced) | `logFrequency_mul_logPeriod` (definitional unfold) | ω-inversion: `∀ ω > 0, (√3-shift property) → ω = 2π/log 3` (**class B — the recommended landing**) | If `α_NS / α_RH` could be identified with such an ω, L5 would follow. Currently no such identification exists. |
| **T2** | `sigma(α) = log₃ ‖1 + 2 cos(πα)‖` | `SigmaAbscissa_r212.lean:235`, `SubstrateOscillator_r223.lean` | **YES** | **YES** | α-indexed | closed form (definitional) | **E + F** | no | `corpus_constant_amplitude_dichotomy` (r223:236) | free ω-analog: replace `π α` by `ω α` free, characterize which ω make dichotomy hold | Very speculative. σ is a function of α; even α-free would not directly give L5. |
| **T3** | `lambda0(α) := π / (10 α)` | `AlphaFromSubstrateKTheory_r123.lean:424` | **YES** | **YES** | universal coupling | `λ₀·α = π/10` (definitional) | **E + F** | no | `coupling_H3_identity_holds_for_every_alpha` (r123:430) | H3 identity `sin(π/10) = 1/(2φ)` (mathlib) | Not L5-relevant. Uniform in α (non-selective). |
| **T4** | Transfer operator `T3` | `TransferOperator.lean:586` (approx) | no | no | yes (base-3) | bounded (`‖T3‖ ≤ 1`), not computed | **N/A (no π yet)** | no | self-adjointness, formal adjoint | eigenvalues (Clay-grade Mayer/Hilbert-Pólya) | If any eigenvalue equalled π, class A. Not attempted. |
| **T5** | Transfer operator `T3_sym` | `TransferOperator.lean:700` (approx) | no | no | yes | discrete spectrum acknowledged; not computed | **N/A** | no | self-adjointness | eigenvalue computation | Class A if eigenvalue = π. Not attempted. |
| **T6** | Continuous spectral measure attempt | `T3SymContinuousSpectralMeasureAttempt.lean` | possibly | no | proposed | scaffold only | **N/A** | yes (this is why the attempt exists) | none discharging | continuous measure of T3_sym | Would require substrate reformulation. |
| **T7** | Modular fundamental domain area | `RHViaH3PerelmanBridge.lean:109` | **YES** | no | classical (PSL(2,ℤ)\ℍ) | `area = π/3` by def | **C + E** | no (classical) | none | none — this is classical geometry | Would need PF-substrate derivation of PSL(2,ℤ)\ℍ. Absent. |
| **T8** | Sphere `S²` area | `RHViaH3PerelmanBridge.lean` (approx line 130) | **YES** | no | classical | `= 4π` by def | **C** | no | none | none — external classical | Not L5-relevant. |
| **T9** | Gaussian `gaussianReal 0 1` | `YM_BochnerMinlosR4Witness.lean` (via `MeasureTheory.integral_gaussian`) | **YES** in mathlib def | no | mathlib | integral = `√(2π)` | **C + D** | (Fourier convention) | none formalizing self-duality | Gaussian self-duality **NOT PROVED IN CORPUS**; would be class B target if formalized properly. See §9. |
| **T10** | `θ`, `ξ`, `completedRiemannZeta*` | `Analytic/Xi*.lean`, `CompletedZeta0Mellin*.lean` | **YES** (via mathlib) | no | mathlib | many facts (r305–r315) | **C + D + E** | no (functional-equation-forced) | r315 `Xi_15_pos`; r310–r312 mellin identities | π-derivation would require self-dual FE proof from π-free hypothesis; corpus uses `hurwitzEvenFEPair 0` which has π-content in its definition | Not directly L5. |
| **T11** | H₃ Coxeter identities | `H3CoxeterOrigin.lean` | **YES** (via `Real.cos_pi_div_five`) | no | classical | `cos(π/5) = φ/2`, `sin(π/10) = 1/(2φ)` | **C** | no | multiple; all use mathlib | none needed — these are `Real.cos_pi_div_five` etc. | φ is characterized by H3 (external), NOT by PF substrate. |
| **T12** | Substrate trace range `ℤ[1/3]` | `AlphaFromSubstrateKTheory_r123.lean:127` | no | no | yes | `ℤ[1/3]` (rational) | **N/A (excludes π)** | no | r320 `memZ13_ratio_ne_pi` | **ruled out** by r320 as π-carrier | Directly excluded from carrying π. |

## 9. Fourier / theta self-duality — detailed status

Per DIRECTIVE Part VI, this is the most-interesting-possible route. Detailed findings:

### The BAD pattern in mathlib

`MeasureTheory.integral_gaussian` and `Real.fourierIntegral` machinery in mathlib supports statements like `Fourier(exp(-π x²)) = exp(-π x²)` — with `Real.pi` already in the Gaussian's definition. This is tautological for our purposes.

### The GOOD pattern

Ideal candidate theorem:
```lean
theorem gaussian_self_dual_scale_unique {a : ℝ} (ha : 0 < a)
    (hself : ∀ x, fourierIntegral (fun x => exp (-a * x^2)) x = exp (-a * x^2)) :
    a = Real.pi
```

**Present in PF corpus?** NO.

**Present in mathlib?** The core self-duality of the Gaussian is proved for the specific `π`-normalized case (`Real.fourierIntegral_gaussian` or similar), not as a characterization result for free `a`. A formalization of the characterization would require:

1. Choose a fixed Fourier convention (mathlib uses `fourierIntegral f x = ∫ f t * exp(-2π i t x) dt`).
2. Prove `Fourier(exp(-a x²)) = √(π/a) · exp(-π² x² / a)`.
3. Impose self-duality: `√(π/a) · exp(-π² x² / a) = exp(-a x²)` pointwise → `a = π` (up to convention).

The problem: **the value `a = π` is convention-dependent.** With the `e^(-2π i t x)` convention, self-duality forces `a = π`. With the `e^(-i t x)` convention, self-duality forces `a = 1/2` and the recovered constant is `√(2π)`, not π directly.

**Consequence.** A Gaussian-self-duality characterization DOES exist mathematically, but its numerical output depends on the convention. Landing it in Lean would require choosing mathlib's Fourier convention and reporting `a = π` in that convention specifically. The DIRECTIVE Part VI warns: "Do not manipulate conventions to force π. Therefore the meaningful invariant may be a DIMENSIONLESS relation rather than the literal number π."

### Assessment

A Gaussian-self-duality characterization landing would be **class B**, but its numerical output is convention-tied. The theorem's true content is "the Gaussian is scale-invariant under the canonical Fourier transform," which is a genuine mathematical fact — one that mathlib supports. Formalizing this in PF would require Fourier-transform machinery not currently present in the corpus (nothing in `PF/**` uses `Real.fourierIntegral` in a self-duality proof).

**Not the smallest tractable landing.** It would be a significant Fourier-infrastructure addition. Compare with the r222-inversion candidate (T1), which requires only trigonometry and mathlib's `Real.cos_eq_zero_iff` / `Real.log` machinery — no Fourier infrastructure.

## 10. Modular / KMS / crossed-product / nontracial — detailed status

### Explicit results

- **r113 `substrate_UHF_trace_unique`** (`PF/SubstrateTraceUniqueness.lean:76`) — every continuous unital tracial functional on `T_∞` equals the canonical UHF trace.
- **r123 `substrate_tracial_state_space_singleton`** — an immediate consequence.

### KMS obstruction (informal argument)

A KMS state at inverse temperature β ≠ 0 for a nontrivial modular automorphism group σ_t on `T_∞` would:
1. Restrict to the σ-fixed-point subalgebra as a tracial state.
2. Extend by GNS to a normal state on the associated von Neumann algebra.
3. Give rise to a modular flow non-trivially.

But r113 gives uniqueness of tracial state on `T_∞`, and no proper von Neumann completion of `T_∞` is constructed in the corpus. Hence there is no formalized KMS enrichment path. **The corpus does not attempt one.**

### Crossed products

Neither `T_∞ ⋊_α ℤ` nor `T_∞ ⋊_α ℝ` nor any rotation algebra `A_θ` is defined in the corpus. Such constructions would exit the current substrate and inject irrational scale via θ (in `A_θ`, K-theory is `ℤ + θℤ`). **No such construction exists in the formalized corpus.**

### Comment-only references

- `Analytic/HilbertPolyaIdentificationPrecise.lean`: docstring mentions "KMS state analytic continuation" and "Bost-Connes C* dynamical system" as *external comparators*, not as formalized objects.
- `RHViaH3PerelmanBridge.lean`: mentions "modular surface" as geometric reference to `PSL(2,ℤ)\ℍ`, not as substrate modular flow.

**Verdict.** No modular / KMS / crossed-product π-carrier exists in the corpus, and r113 forbids the tracial route. Enriching this layer would require substantial new infrastructure and would exit the current substrate.

## 11. Non-π law generators — cross-reference to L1–L4, I6, I7, I9

Per DIRECTIVE Part IX. If a candidate generator could explain more than L5 alone, it outranks single-purpose generators.

| Candidate | L1 (φ minpoly) | L2 (√2 minpoly) | L3 (`1/4` offset) | L4 (`√(2π)` minpoly) | L5 (`π` scaling) | I6 (`α_YM · α_BSD`) | I7 (`α_Po + 1`) | I9 (`3` in RH·YM) |
|---|---|---|---|---|---|---|---|---|
| **T1 ω-inversion (proposed class B)** | | | | (peripherally, via `√(2π)` characterization if extended) | **PRIMARY** | | | |
| **H_3 icosahedral (external)** | ✓ (φ from `cos(π/5)`) | | (via top-exponent gap?) | | | | | |
| **base-3 substrate `3`** | | | | | | | | ✓ (RHS = 3) |
| **Gaussian self-duality** | | | | ✓ (`√(2π)` from Gaussian norm) | possibly (via `2π` characterization) | | | |
| **T3 spectral (WIP)** | | | | | | | | |
| **Perelman anchor (external)** | | | | | | | ✓ (`α_Po = 1` as external input) | |

The r222-inversion T1 candidate directly targets L5. It does not itself explain L1, L2, L3, L4, I6, I7, or I9. Its **cross-law leverage is limited to L5 and — after significant extension — possibly L4** (since `√(2π)` involves the same `2π` factor).

The strongest cross-cutting cross-law candidate remains **H₃ icosahedral** for L1 (via `cos(π/5)`); but H₃ has no proved intrinsic connection to base-3 substrate, per the prior intrinsic-origin audit §11.

## 12. 9-criterion ranking of candidates

Ordering per DIRECTIVE Part VIII:

| Criterion | T1 (ω-inversion) | Gaussian self-duality | T3_sym spectrum | H₃ intrinsic |
|---|---|---|---|---|
| 1. Independence from α | ✓ (ω, √3 both α-free) | ✓ | ✓ | ✓ |
| 2. Independence from π | ✓ (ω free, √3 base-forced) | ✓ if free `a` | ✓ | ✓ if constructed intrinsically |
| 3. Canonicity | ✓ (√3 = √(base)) | ✓ | ✓ | requires new theorem |
| 4. Uniqueness / selectivity | ✓ (elementary trig) | ✓ (convention-dependent) | conjectural | conjectural |
| 5. PF-native centrality | high (r220-r223 is 4-file substrate infra) | low (Fourier infra absent) | high (T3 is central) | high (H₃ narrative is central) |
| 6. Compatibility with current substrate | ✓ (no new substrate object needed) | requires Fourier infra addition | requires spectral-computation infra | requires new substrate-symmetry theorem |
| 7. Theorem tractability | **very high** (elementary trigonometry, ~30 lines) | medium (Fourier infra needed) | very low (Clay-grade Hilbert-Pólya) | very low (requires substrate-symmetry theorem) |
| 8. Usefulness for L5 | high (directly characterizes the π-content of the ansatz) | medium (Gaussian norm ≠ L5 shape) | high if it works | none (does not touch L5) |
| 9. Reuse across other laws | limited (T1 is L5-focused) | some (L4 via `√(2π)`) | potentially many | L1 |

**Ranking:**
1. **T1 (r222 ω-inversion)** — highest across tractability + PF-central + L5-useful.
2. Gaussian self-duality — mathematically deeper but infrastructure-heavy; convention-dependent output.
3. H₃ intrinsic — highest scientific value but requires substrate-symmetry theorem currently absent.
4. T3_sym spectrum — Clay-grade; not smallest.

## 13. Recommended next theorem

Per DIRECTIVE Part X. Preference order: Type 1 > Type 2 > Type 3.

### Recommendation: **TYPE 1 (positive characterization)** — the r222 ω-inversion

Precise statement (READ-ONLY recommendation; NOT implementing):

```lean
/-- **Characterization of `logFrequency`.**  In the log-cosine ansatz family
`g_ω(a) := A · a^σ · cos(ω · log a + φ₀)` (with `ω : ℝ` a free positive parameter),
the base-3-canonical property "the next zero of `g_ω` after `a > 0` occurs at
`√3 · a`" forces `ω = 2π / Real.log 3`. -/
theorem logFrequency_characterized_by_sqrt3_shift
    {ω : ℝ} (hω : 0 < ω)
    (hshift : ∀ (A σ φ₀ a : ℝ), A ≠ 0 → 0 < a →
      NextZero (fun t => A * t^σ * Real.cos (ω * Real.log t + φ₀)) a =
      Real.sqrt 3 * a) :
    ω = 2 * Real.pi / Real.log 3
```

(Exact hypothesis form depends on how the r222 `NextZero` operator is formalized. The essence: an arbitrary free-parameter ω, given the √3-shift canonical requirement, is uniquely characterized as `2π / log 3`.)

**Elementary proof sketch.**
1. `Real.cos_eq_zero_iff`: `cos θ = 0 ↔ ∃ k : ℤ, θ = (2k + 1) π / 2`.
2. If `a` is a zero of `g_ω`, then `ω · log a + φ₀ = (2k+1) π / 2` for some `k`.
3. Next zero at `a' = c · a` (for the minimal `c > 1` producing another zero) requires `ω · log(c · a) + φ₀ = (2k+3) π / 2`, i.e., `ω · log c = π`.
4. Setting `c = √3` gives `ω · (log 3)/2 = π`, hence `ω = 2π / log 3`.
5. The universal quantifier over `A, σ, φ₀, a` collapses because the shift is independent of these (see r222:23 "The multiplier `√3` depends on `logFrequency` alone").

**Class assignment.**
- **Class B (characterization) in the PF frame:** the free positive parameter ω is *forced* by the base-canonical √3-shift property to equal a specific π-valued expression.
- **Class C (external classical) in the absolute frame:** the π comes from the period of `Real.cos`, which is external mathlib. This is the honest scope — DIRECTIVE Part XI is emphatic that we must not confuse "PF characterizes π-valued parameter" with "PF generates π."

**Type designation:** **Type 1 — positive characterization** per DIRECTIVE Part X. It converts one currently-definitional π-insertion (`logFrequency := 2π / log 3`) into an *output* of a base-canonical characterization.

**Precise scientific scope.**

**PROVED (if landed):**
- The frequency of any log-cosine ansatz satisfying the substrate-canonical √3-next-zero shift is uniquely `2π / log 3`.
- π is characterized in the PF ansatz setting by a base-canonical property.

**DOES NOT establish:**
- L5 itself, which requires additionally identifying `α_NS / α_RH` with such an ω (STEP B / STEP C of DIRECTIVE Part VII).
- π as originating from the substrate rather than from `Real.cos`.
- Any of L1, L2, L3, L4, I6, I7, I9.
- The α-skeleton architecture as substrate-generated.

**Provenance code change if landed:**
- `logFrequency`: **class E → class B** (its π-content becomes characterized rather than definitional).
- All eight r128 structural laws remain **NOT class A**.
- Overall structural-law provenance: **7/8 unchanged, 1/8 (L5) partially advanced by exposing a candidate π-carrier**.

### Why not an alternative

**Alternative A** — Gaussian self-duality characterization. Rejected as recommendation because: convention-dependent output; requires Fourier-transform machinery not currently in the corpus; smallest tractable formalization is significantly larger than the r222 inversion.

**Alternative B** — H₃ intrinsic substrate-symmetry theorem. Rejected because: requires a fundamentally new theorem (H₃ ≤ Aut of some canonical base-3 substrate object), which is Clay-grade research, not a "smallest testable theorem."

**Alternative C** — T3_sym spectral computation. Rejected because: Clay-grade (Hilbert-Pólya); no eigenvalue is currently computed anywhere; not a small landing.

**Alternative D (Type 3 no-go)** — extend r320 to `Subring.closure (Set.range MemZ13)`. Rejected because: essentially a corollary of r320 + closure-of-ℚ-under-subring-ops, and does not advance the *positive* question the DIRECTIVE Part X prefers.

### DIRECTIVE Part XI guardrail compliance

The recommended theorem does NOT:
- claim π occurs in a theorem = PF generates π;
- confuse `Real.pi` in an unrelated definition with substrate generation;
- extract π from a Gaussian that already contains π;
- manipulate conventions to force π.

It DOES:
- take a π-free free-parameter object (log-cosine family with ω free);
- impose a π-free canonical property (√(base) shift);
- prove the parameter is uniquely forced to a π-valued expression (`2π / log 3`);
- **honestly acknowledge** that the π *origin* is the period of `Real.cos` (external classical mathlib), while the π *placement in the PF ansatz* is a genuine characterization.

## 14. Status lock

Per DIRECTIVE Part XII:

| Result | Status |
|---|---|
| r128 conditional one-anchor rigidity | PROVED |
| Structural-law provenance | 0/8 laws intrinsically PF-derived |
| r320 trace-range ratio for L5 | FORMALLY RULED OUT |
| Class-A / Class-B π-generators in current corpus | **0 currently formalized** |
| Class-B candidate — r222 ω-inversion | **1 tractable candidate identified (not implemented)** |

**Present frontier.** The bare trace-range layer of `T_∞ = 3^∞` produces `ℤ[1/3] ⊂ ℚ` and cannot supply π. The corpus's analytic/spectral/dynamical layers currently either (a) inject π definitionally (r220-r223 log-cosine machinery), (b) cite external classical π-content (H₃, `Real.cos`, mathlib geometry), or (c) leave the relevant spectrum uncomputed (T3, T3_sym).

The r222 ω-inversion is the smallest tractable candidate for converting one definitional π-insertion into a genuine characterization. It does not resolve L5 but it removes one honest gap in the current substrate's transcendental-carrier story.

---

## Summary

The transcendental-carrier audit surveyed 1409 PF Lean files, ~4761 direct `Real.pi` occurrences, ~53 π-containing definitions, and every canonical operator / dynamical / modular / spectral construction in the corpus. It found **zero class-A π-generators** and **zero class-B π-generators currently formalized**. Every π occurrence is E (definition-injected), D (normalization convention), C (external classical), or F (α-injected).

The corpus does not contain: Fourier-transform machinery, Gaussian self-duality (either pattern), KMS states (r113 forbids), crossed products, rotation algebras, nontracial states, or explicit computed spectra for any canonical operator. All π-emergence "attempt" files (T3_sym continuous spectral measure) acknowledge the substrate-reformulation cost.

**One tractable class-B candidate is identified.** The r222 log-cosine ω-inversion: characterize the free positive frequency parameter ω by the base-canonical √(base) next-zero shift, forcing `ω = 2π / log 3`. This is elementary trigonometry (~30 Lean lines) and converts `logFrequency`'s provenance from class E to class B. It does not resolve L5, does not close the intrinsic-origin question, and does not touch any of L1, L2, L3, L4, I6, I7, I9.

**Recommended next theorem (READ-ONLY recommendation; NOT implementing):**

```lean
theorem logFrequency_characterized_by_sqrt3_shift
    {ω : ℝ} (hω : 0 < ω)
    (hshift : ∀ (A σ φ₀ a : ℝ), A ≠ 0 → 0 < a →
      NextZero (fun t => A * t^σ * Real.cos (ω * Real.log t + φ₀)) a =
      Real.sqrt 3 * a) :
    ω = 2 * Real.pi / Real.log 3
```

**Type designation:** Type 1 (positive characterization). Elementary proof; no new mathlib API surfaces; small reuse footprint; converts one E to one B; L5 semantic identification remains separate (STEP B / STEP C of DIRECTIVE Part VII).

**Correct status statement:** the r220-r223 substrate-oscillator machinery inserts π definitionally into `logFrequency`; a base-canonical characterization theorem currently absent would convert this to class B. No PF-native object currently generates π as a substrate output; every existing π placement is either external classical or explicit definition.

**Not implementing without your authorization.** Per DIRECTIVE Part X: STOP after producing this audit.

---

**End of audit.**

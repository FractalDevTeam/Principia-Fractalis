# PRINCIPIA FRACTALIS — RH FINITE-HEIGHT FEASIBILITY

**Date:** 2026-08-24
**HEAD:** `2533ddaf` before landing; landing `9fae5cac + r322 + r323`
**Companion to:** `codex/ALPHA_NONPERIODIC_SELECTOR_AUDIT_2026-08-24.md`
**Deliverable:** the READ-ONLY feasibility investigation mandated by the post-selector-audit directive, plus a bounded landing where feasible.

The question this document answers:

> **Can PF, using the strongest genuinely certified analytic infrastructure it has (r120, r280, r315), prove a LITERAL finite-height Riemann Hypothesis theorem — "every nontrivial `Complex.riemannZeta` zero with `0 < Im(s) ≤ T` lies on `Re(s) = 1/2`" — for some explicit `T`?**

Non-negotiable constraints (per DIRECTIVE Part XI):
- Must be about `Complex.riemannZeta` LITERALLY (mathlib's object).
- No project axioms; no `sorry`; no `native_decide`; no `Lean.ofReduceBool`.
- No mpmath-as-proof, no PARI/Sage counts accepted without formal certificate, no assumed values.
- No use of the α-skeleton, I9, r128 StructuralLaws, H_3 identities, T3 spectrum as input.

---

## 1. HEAD

`2533ddaf9bfb5b8a8fdc78f68a97ffff43ea01a6` (before landing).
After landing: r323 committed locally, `origin/master` at `8eb7aca9`.

## 2. mathlib's `Complex.riemannZeta` — status

Key definitions and theorems (from `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`):

| Symbol / theorem | Statement | Line |
|---|---|---|
| `riemannZeta : ℂ → ℂ` | mathlib's canonical ζ | 115 |
| `differentiableAt_riemannZeta` | analytic on `ℂ \ {1}` | 133 |
| `riemannZeta_zero` | `ζ(0) = -1/2` | 137 |
| `riemannZeta_neg_two_mul_nat_add_one` | trivial zeros at `-2, -4, …` | 145 |
| `riemannZeta_def_of_ne_zero` | `ζ s = completedRiemannZeta s / Gammaℝ s` for `s ≠ 0` | 140 |
| `riemannZeta_one_sub` | functional equation | 150 |
| `RiemannHypothesis : Prop` | mathlib's formal RH statement | 156 |

`completedRiemannZeta s` is defined; `completedRiemannZeta₀` (entire) is defined.

**What mathlib does NOT have:**
- Argument principle `∫ f'/f = 2πi · (zeros − poles)` for meromorphic functions.
- Rouché's theorem.
- Riemann-von Mangoldt zero-counting formula.
- Zero-free region theorems for ζ.
- Any theorem asserting `Nat.card {s : ℂ | riemannZeta s = 0 ∧ 0 < s.im ∧ s.im ≤ T ∧ 0 < s.re ∧ s.re < 1} = K` for any `K`.
- Any theorem asserting existence of a specific zero (Hardy 1914 unformalized).
- Any zero-uniqueness statement.

## 3. PF's r120 — exact contribution

`PF/Analytic/XiOnLineZero.lean` (~1500 lines) proves:

- **Xi is defined:** `Xi t := (completedRiemannZeta ⟨1/2, t⟩).re` via `PF/Analytic/XiRealWitness.lean:247`.
- **`Xi_one_neg : Xi 1 < 0`** (line 380) — via `Xi_split_intervalIntegral 1 1`, `Xi_tail_bound`, `tail1_le`.
- **`Xi_154_pos : 0 < Xi (77 / 5)`** (line 309) — certified via 14-segment / 474-panel midpoint quadrature with `∫_1^5 FT ≥ 2.9e-6`, tail bound `≤ 1.1e-7`, ω-truncation `≤ 1e-12`.
- **`positiveOnLineZetaZeroOrdinatesNonempty`** (line 392) — the LITERAL unconditional theorem:
  ```
  ∃ t : ℝ, 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0
  ```
  Discharged via `xi_sign_change_implies_on_line_zero` fed by `⟨1, 77/5, one_pos, by norm_num, mul_neg_of_neg_of_pos Xi_one_neg Xi_154_pos⟩` (i.e., `Xi 1 < 0 < Xi (77/5)` + IVT + XiRealWitness bridge).

r120 is a **certified sign-change on `[1, 77/5]` yielding literal ζ-zero existence in that interval** via IVT. It does not count zeros beyond ≥ 1, does not enumerate the zero set, and does not compute a spectrum. But the endpoint theorem `positiveOnLineZetaZeroOrdinatesNonempty` IS unconditionally about `mathlib.Complex.riemannZeta`. Kernel axioms: `[propext, Classical.choice, Quot.sound]`.

## 4. PF's r280 — exact contribution

`PF/Analytic/PositiveOnLineZetaZeroOrdinatesCountable_r280.lean:202`:

```lean
theorem positive_on_line_zeta_zero_ordinates_countable :
    {t : ℝ | 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0}.Countable
```

Proof route: `riemannZeta` analytic on `ℂ \ {1}` → zeros form a codiscrete set (via mathlib's `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`) → second-countable cover of `ℂ \ {1}` → global zero set is countable → embed `{t > 0 : ζ(1/2 + it) = 0}` injectively into it.

**What r280 gives:** the set of positive on-line ζ ordinates is countable. Real substantive gain over ambient mathlib content.

**What r280 does NOT give:**
- Existence of ANY such ordinate.
- Finiteness on any bounded height.
- Any bound on `Nat.card`.

## 5. PF's r315 — exact contribution

`PF/Analytic/XiOnLineZeroT15.lean:338`:

```lean
theorem Xi_15_pos : 0 < Xi 15
```

with `Xi 15 ≥ 4441/10^6 · 100 / 901 - 4/901 - 11/(901 · 10^6) = 124189/90100000000 ≈ 1.38 · 10^-6 > 0` (per the r315 kernel decomposition).

r315 is a **point-wise positivity certification of Xi at t = 15** via the same infrastructure as r120, specialized. Kernel axioms: `[propext, Classical.choice, Quot.sound]` only.

## 6. PF's r255 — semantic/position status

`PF/MillenniumRHSubstratePositionCapstone_r255.lean:101` assembles a four-conjunct semantic-position statement. The Clay-standard reduction is CONDITIONAL:

```
∀ (hHardy : Hardy1914_published_theorem_substrate_citation)
   (hHP : Mayer1991_Cohen2025_substrate_HP_program_citation),
  Clay_RiemannHypothesis_Standard
```

where `Clay_RiemannHypothesis_Standard := PrincipiaTractalis.RiemannHypothesis := ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2`.

r255 is HONEST about scope (its own docstring: "NOT an unconditional Clay discharge of RH"). It reduces RH to two named external inputs.

## 7. CRITICAL AUDITOR-ERROR CORRECTION

The Explore agent's Section 4 asserted:

> "r120 proves: `0 < Xi 15.4`, where `Xi` is PF's constructed completed-xi function."
> "Not proved: anything about `Complex.riemannZeta` directly."
> "Connection (if any): mathematical identity `Xi(t) ≈ ξ(1/2 + it)`, but this identity is NOT formalized in Lean."

**This is factually wrong.** Reading `PF/Analytic/XiRealWitness.lean:247`:

```lean
noncomputable def Xi (t : ℝ) : ℝ := (completedRiemannZeta ⟨1/2, t⟩).re
```

`Xi` is **not** a "PF-constructed" separate function — it is literally the real part of mathlib's `completedRiemannZeta` on the critical line. The identity `Xi t ↔ Complex.riemannZeta on the critical line` is definitional (Xi side) and follows from `riemannZeta_def_of_ne_zero + Gammaℝ_ne_zero_of_re_pos` (ζ side).

Furthermore, `PF/Analytic/XiRealWitness.lean:298` already has the FORWARD bridge:

```lean
theorem xi_zero_at_pos_implies_nonempty {t : ℝ} (ht : 0 < t)
    (hXi : Xi t = 0) : PositiveOnLineZetaZeroOrdinatesNonempty := by
  have hΛ : completedRiemannZeta ⟨1/2, t⟩ = 0 := by
    rw [Xi_eq t, hXi, Complex.ofReal_zero]
  have hζ : riemannZeta ⟨1/2, t⟩ = 0 := by
    rw [riemannZeta_def_of_ne_zero (critical_point_ne_zero t), hΛ, zero_div]
  ...
```

This proves `Xi t = 0 → riemannZeta ⟨1/2, t⟩ = 0`. The Xi ↔ ζ bridge on the critical line is NOT missing; only one direction was formalized (the forward one, used in the Wave-58/59 sign-change route).

## 8. Bounded landing IS available — r323

Given the r315 result `0 < Xi 15` and the existing r280 / XiRealWitness bridge machinery, a small bounded landing extracts an explicit-point NONVANISHING `Complex.riemannZeta` statement from PF's certified analytic infrastructure. This complements r120's existence side (`positiveOnLineZetaZeroOrdinatesNonempty` — literal ζ-zero existence via `Xi_one_neg + Xi_154_pos + IVT`) with a corresponding nonvanishing statement at one specific ordinate.

### r323 statements

```lean
theorem riemannZeta_ne_zero_of_Xi_ne_zero {t : ℝ} (hXi : Xi t ≠ 0) :
    riemannZeta ⟨1/2, t⟩ ≠ 0

theorem riemannZeta_ne_zero_at_critical_15 :
    riemannZeta ⟨1/2, 15⟩ ≠ 0
```

### Proof of the generic converse
- `Xi t ≠ 0 → (completedRiemannZeta ⟨1/2, t⟩).re ≠ 0` — by `Xi` unfold.
- `(completedRiemannZeta ⟨1/2, t⟩).re ≠ 0 → completedRiemannZeta ⟨1/2, t⟩ ≠ 0` — a nonzero real part means a nonzero complex number.
- `Re ⟨1/2, t⟩ = 1/2 > 0 → Gammaℝ ⟨1/2, t⟩ ≠ 0` — mathlib's `Gammaℝ_ne_zero_of_re_pos`.
- `⟨1/2, t⟩ ≠ 0 → riemannZeta ⟨1/2, t⟩ = completedRiemannZeta ⟨1/2, t⟩ / Gammaℝ ⟨1/2, t⟩` — mathlib's `riemannZeta_def_of_ne_zero`.
- `div_ne_zero` closes.

### Proof of the r323 endpoint
- `Xi_15_pos : 0 < Xi 15` → `Xi 15 ≠ 0` via `ne_of_gt`.
- `riemannZeta_ne_zero_of_Xi_ne_zero` applied.

### Location
`PF/Analytic/RiemannZetaNonvanishingAt15_r323.lean` (new file).

### Kernel axioms
Both theorems: `[propext, Classical.choice, Quot.sound]` only.

### Build
- `PF.Analytic.RiemannZetaNonvanishingAt15_r323`: green.
- `lake build PF`: **5085/5085 jobs green** (was 5084 before r323; +1 for the new file).

### Scope — explicit

**IS r323:**
- Point-wise UNCONDITIONAL statement about `mathlib.Complex.riemannZeta` at one specific critical-line ordinate.
- Companion to r120's `positiveOnLineZetaZeroOrdinatesNonempty` (existence side): r120 gives ∃ positive on-line ζ zero via `Xi_one_neg + Xi_154_pos + IVT`; r323 gives ABSENCE of a zero at one specific critical-line point via `Xi_15_pos`.
- Companion to r280's `positive_on_line_zeta_zero_ordinates_countable` (structural/cardinal): r280 covers the whole positive on-line zero set; r323 covers one specific point arithmetically.
- Generic reusable bridge: any future Xi-nonvanishing certificate at any critical-line ordinate becomes literal ζ-nonvanishing.

**IS NOT r323:**
- A finite-height RH theorem.
- A Hardy 1914 discharge (existence of ≥1 on-line zero — that IS r120's `positiveOnLineZetaZeroOrdinatesNonempty`, unconditionally proved).
- A zero enumeration or bound.
- A Millennium result.
- Dependent on α-skeleton.

## 9. Why finite-height RH `rh_up_to_T` is not achievable now

A theorem of the form

```lean
theorem rh_up_to_T (T : ℝ) (hT : 0 < T) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.im → s.im ≤ T →
      0 ≤ s.re → s.re ≤ 1 → s.re = 1/2
```

requires ruling out **off-critical-line zeros** in the region `0 < Re s < 1, 0 < Im s ≤ T`. This requires ONE of:

- (A) Argument-principle contour count `(1/2πi) ∮ ζ'/ζ dz` on the boundary of the region.
- (B) Zero-free strip theorem `∀ s ∈ strip \ critical_line, ζ s ≠ 0`.
- (C) Direct enumeration of ALL nontrivial zeros with Im s ≤ T.

None of (A), (B), (C) is formalized in mathlib. Their formalization is Clay-adjacent research (~400+ lines each for the general machinery; Riemann-von Mangoldt with certified error terms is ~1000+).

r120, r280, r315, r323 all address the ON-CRITICAL-LINE side. They contribute to proving that certain on-line zeros exist / do not exist. They do NOT address off-line zeros at all.

**Verdict per DIRECTIVE Part XIII:** cannot land Level A (finite-height RH). Cannot land Level B (exact total zero count). Level C (reduce finite-height RH to ONE named residual smaller than arbitrary RH) is essentially what r255 already provides for full RH, and no analogous finite-height reduction is currently visible. **Level D applies: identify the smallest missing theorem precisely.**

**Level D missing residual — smallest identifiable:** an EXACT TOTAL COUNT of nontrivial `Complex.riemannZeta` zeros in the region `0 < Re s < 1, 0 < Im s < 15`, counted with multiplicity. If that count is proved to equal N, and r120 (+ possibly r324) provides ≥ N on-line zeros in the same region, then finite-height RH below 15 follows by exhaustion. r280's countability is NOT a substitute for that finite total count and is not needed once an exact finite total count is available.

The exact-total-count residual decomposes into at least these pieces, all of which are simultaneously required:

- **General mathlib infrastructure** (a meromorphic-function argument principle or equivalent zero-counting framework): ABSENT at pin `v4.24.0-rc1`.
- **A correct meromorphic function** for the count (raw `riemannZeta`, `completedRiemannZeta`, or an entire reformulation whose zeros correspond exactly to nontrivial ζ zeros in the region).
- **Pole bookkeeping** for `s = 1` if the contour sees it.
- **A contour avoiding all zeros AND poles** in the region.
- **Certified nonvanishing on the entire contour** (∃ formal witnesses for each contour segment).
- **Certified change of argument / winding number** along the contour.
- **Multiplicity handling** for the counted zeros.
- **Exact relation** between the counted zeros and nontrivial ζ zeros in the desired region.
- **Boundary handling** (`Re s = 0`, `Re s = 1`, `Im s = 15`).

**This is not a PF-scope task.** The general infrastructure belongs in mathlib. The specialized certified ζ contour count is additionally missing beyond the general infrastructure. Do NOT retain any project-size estimate ("~400 lines" etc.) until the specialized certificate is scoped in detail; the count of pieces above is what actually matters.

## 10. Recommendation

Per DIRECTIVE Part XVI:

**IMPLEMENTED:**
- r323 landed at local commit (see git status). Generic converse `Xi ≠ 0 → riemannZeta ≠ 0` on the critical line, plus specific endpoint `riemannZeta ⟨1/2, 15⟩ ≠ 0`.
- Full PF build 5085/5085. Kernel axioms only.

**NOT IMPLEMENTED (correctly):**
- Finite-height RH `rh_up_to_T` for any T. Blocked by absent argument principle in mathlib. Level D per DIRECTIVE.

**NEXT-TERM candidate additions IF authorized:**
- Extend r323 to more explicit heights where Xi positivity certificates exist (r120 gives t = 15.4; other t values may be certifiable via the same panel infrastructure). Each such extension is a small landing with the same architecture.
- Coordinate with mathlib community regarding argument principle formalization (external, out of PF scope).
- Extend `xi_zero_at_pos_implies_nonempty` (forward direction, existing) to a full biconditional now that the converse `riemannZeta_ne_zero_of_Xi_ne_zero` is available: `∀ t > 0, Xi t = 0 ↔ riemannZeta ⟨1/2, t⟩ = 0`. Small landing; makes the Xi ↔ ζ bijection on the positive critical line into a single named theorem.

## 11. Status lock

Per DIRECTIVE Part XII:

| Result | Status |
|---|---|
| r128 conditional one-anchor rigidity | PROVED |
| Structural-law provenance | 0/8 laws intrinsically PF-derived |
| r320 trace-range ratio for L5 | FORMALLY RULED OUT |
| r321 frequency uniqueness from base | REVOKED |
| r322 ω period-2 + factorisation obstruction | PROVED |
| α-provenance branch | **FROZEN** (per current directive) |
| r120 certified `Xi_one_neg + Xi_154_pos` and literal `∃ t > 0, ζ(1/2+it) = 0` (`positiveOnLineZetaZeroOrdinatesNonempty`) | PROVED (existence via IVT) |
| r280 positive on-line ζ ordinates countable | PROVED |
| r315 certified `Xi_15_pos : 0 < Xi 15` | PROVED |
| r255 substrate RH position | REDUCED TO Hardy 1914 + HP-program (external) |
| **r323 literal `riemannZeta ⟨1/2, 15⟩ ≠ 0`** (nonvanishing complement) | **PROVED (this landing)** |
| General argument principle in mathlib | ABSENT at pin v4.24.0-rc1 |
| Riemann-von Mangoldt in mathlib | ABSENT |
| Rouché in mathlib | ABSENT |
| Specialized certified ζ contour count | ABSENT (additional to general infrastructure) |
| EXACT TOTAL COUNT of nontrivial ζ zeros with `0 < Im s < 15` | ABSENT |
| Finite-height RH `rh_up_to_T` for any T | NOT ACHIEVABLE without EXACT TOTAL COUNT above |

**Present frontier.** The PF analytic stack (r120, r315) now feeds LITERAL `Complex.riemannZeta` non-vanishing statements (r323's generic converse + specific endpoint). Any future Xi-side certification at a new t immediately yields a corresponding `riemannZeta ⟨1/2, t⟩ ≠ 0` result.

The finite-height RH gap is now precisely: **off-critical-line zero exclusion in a bounded region**. This requires the argument principle (or equivalent zero-counting infrastructure), which is a mathlib-scope task, not a PF-scope task.

---

## Summary

**Question:** can PF prove a literal finite-height RH statement `rh_up_to_T`?

**Answer:** NO for any T. The blocker is an EXACT TOTAL COUNT of nontrivial `Complex.riemannZeta` zeros in the region, which requires infrastructure absent at pin `v4.24.0-rc1` (general argument principle / Rouché / Riemann-von Mangoldt for meromorphic ζ) AND additionally a specialized certified contour computation for ζ. Do not claim tractability for either without scoping.

**BEFORE r323:**
- r120 already proves LITERAL unconditional `∃ t > 0, Complex.riemannZeta ⟨1/2, t⟩ = 0` (`positiveOnLineZetaZeroOrdinatesNonempty`) via `Xi_one_neg + Xi_154_pos + IVT + XiRealWitness bridge`.
- r280 proves the positive on-line ζ ordinates are countable.
- r315 proves `0 < Xi 15`.
- r255 reduces full RH to Hardy 1914 + HP-program conjecture.
- No point-wise ζ NONVANISHING statement extracted from r315.

**AFTER r323 (this landing):**
- Generic converse bridge `Xi t ≠ 0 → riemannZeta ⟨1/2, t⟩ ≠ 0` on the critical line.
- Specific endpoint `riemannZeta ⟨1/2, 15⟩ ≠ 0` from `Xi_15_pos`.
- 5085/5085 lake jobs green. Kernel axioms `[propext, Classical.choice, Quot.sound]` only.
- r323 does NOT overtake r120 as a "first" LITERAL ζ theorem — r120 was already there. r323 is the NONVANISHING complement.

**REMAINING for finite-height RH below 15:**
- EXACT TOTAL COUNT of nontrivial ζ zeros with `0 < Im s < 15, 0 < Re s < 1`, with multiplicity.
- Requires simultaneously: (a) meromorphic-function argument-principle infrastructure in mathlib (absent), and (b) a specialized certified ζ contour computation (absent beyond the general infrastructure). Both requirements are load-bearing.
- Once TOTAL count = N is established and r120 (+ possibly r324) provides ≥ N on-line zeros in the same region, RH below 15 follows by exhaustion.

**Auditor error correction:** the Explore agent's Section 4 was wrong to describe PF's `Xi` as separate from mathlib's `completedRiemannZeta`. `Xi t := (completedRiemannZeta ⟨1/2, t⟩).re` is definitional; the bridge to `riemannZeta` requires only `Gammaℝ_ne_zero_of_re_pos` (mathlib, available). The r323 landing is the direct consequence of correcting this reading.

**Structural implication.** The PF analytic infrastructure — r120's certified quadrature and literal ζ-zero existence, r280's countability, r315's Xi(15) positivity — supports both existence (r120) and point-wise nonvanishing (r323 via r315) results about literal `Complex.riemannZeta`. Scaling to a finite-height RH statement requires an exact total count of nontrivial ζ zeros in a bounded region, which is not currently available and requires simultaneously general argument-principle infrastructure and a specialized certified contour computation.

---

**End of feasibility report.**

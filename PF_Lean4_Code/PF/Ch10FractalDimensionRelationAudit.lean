/-
# Ch 10 — The Fractal-Dimension Relation Is Unestablished (2026-10-05)

## Why this file exists

On 2026-10-05 an earlier pass of this campaign "repaired" twelve sites in
`ch10_hydrodynamic.tex` by replacing the value `5/3` with `8/3` throughout,
on the strength of the chapter's own line (`ch10:353`):

> "The fractal dimension is `d_f = 3 − ζ₂/2` for the second-order function. In
> Kolmogorov theory (no intermittency), `ζ₂ = 2/3`, giving `d_f = 3 − 1/3 =
> 8/3`."

**That identity is itself unestablished, and the repair propagated it.** The
chapter gives no derivation of `d_f = 3 − ζ₂/2`, it is not a relation of the
standard multifractal formalism, and it fails the one baseline check that
formalism supplies. Making twelve sites consistent with an unjustified premise
is worse than the inconsistency it replaced, because the result looks settled.

This file records what is and is not established, and proves the failure of the
baseline check. It does **not** supply a replacement value: see §5.

## What IS established (standard turbulence theory)

* **K41 scaling.** `ζ_p = p/3`, hence `ζ₂ = 2/3`. (Kolmogorov 1941.)
* **The multifractal formalism.** Velocity increments `δu(ℓ) ∼ ℓ^h` on a set of
  Hausdorff dimension `D(h)`, and the structure-function exponents are the
  Legendre transform
  `ζ_p = inf_h [ p·h + 3 − D(h) ]`,
  the `3` being the dimension of physical space and `3 − D(h)` the codimension.
  (Parisi–Frisch 1985; Frisch, *Turbulence*, ch. 8.)
* **K41 is the space-filling case.** K41 has `h = 1/3` with `D(1/3) = 3`, the
  full space, which returns `ζ_p = p/3 + 3 − 3 = p/3`. Non-trivial
  intermittency is precisely the statement `D < 3`. So **in K41 the dimension
  is `3`, not `8/3`.**
* **The β-model.** For a single active fractal of dimension `D`, flux constancy
  gives `δu ∼ ℓ^{(D−2)/3}` on an active fraction `ℓ^{3−D}`, hence
  `ζ_p = (3 − D) + p(D − 2)/3`.
  This satisfies `ζ_3 = 1` **identically in `D`** — the exact Kolmogorov 4/5-law
  constraint — and at `p = 2` gives `ζ₂ = (5 − D)/3`, i.e. `D = 5 − 3ζ₂`, which
  returns `D = 3` at `ζ₂ = 2/3`. (Frisch–Sulem–Nelkin 1978.)

## What is NOT established

**The chapter's `d_f = 3 − ζ₂/2`.** No derivation is given anywhere in ch10.
It is not the Legendre relation, and it fails the K41 baseline in two
independent directions:

* **Forward.** At `ζ₂ = 2/3` it returns `8/3 ≈ 2.667`, where the formalism
  returns `3`. (`asserted_fails_K41_baseline`)
* **Backward.** Inverted it reads `ζ₂ = 6 − 2 d_f`, so the space-filling case
  `d_f = 3` is sent to `ζ₂ = 0` — the no-scaling case — whereas K41 has
  `ζ₂ = 2/3`. (`asserted_inverse_sends_spacefilling_to_zero`)

The β-model relation passes both (`beta_model_passes_K41_baseline`,
`beta_model_satisfies_four_fifths_law`). So a correct relation of this general
shape exists; the chapter's is not it.

## The disagreement is material, not cosmetic

With the chapter's intermittency correction `δζ₂ = (π/10)(ch₂/0.95)` and
`ch₂ ∈ [0, 0.95]`:

| | at `ch₂ = 0` (K41 limit) | at `ch₂ = 0.95` |
|---|---|---|
| chapter, `8/3 − (π/20)(ch₂/0.95)` | `8/3 ≈ 2.6667` | `≈ 2.5096` |
| β-model, `3 − (3π/10)(ch₂/0.95)` | `3` | `≈ 2.0575` |

The two disagree at **both** ends, and the slope differs by a factor of six
(`−1/2` versus `−3` in `ζ₂`). The `ch₂ = 0` column is the K41 limit, where the
answer is known — and the chapter's relation gets it wrong.
`ranges_are_materially_different` below.

## §5 — What this file does NOT do

It does **not** substitute the β-model for the chapter's relation. That would
repeat the original error in a new costume. The β-model is used here only as a
*witness* that the baseline check is passable — it is one multifractal model
among several (She–Lévêque, log-normal, log-Poisson each give a different
`D(h)` and hence a different `ζ₂ ↦ D`), and nothing in ch10 says which model
is intended, or indeed that a single `d_f` is the right object rather than a
spectrum `D(h)`.

Consequently:

* Every quantitative `d_f` figure in ch10 — `8/3`, `π/20`, `2.510`, `2.57`,
  and the `d_f ≤ 8/3` vorticity bound — is **model-dependent and currently
  underived**, and the twelve-site `5/3 → 8/3` substitution did not change that.
* The chapter's *structural* claim survives in shape: intermittency reduces the
  dimension below its K41 ceiling, and the ceiling is approached as `ch₂ → 0`.
  Only the ceiling's value and the coefficient are unestablished.
* Choosing the multifractal model, or replacing the single `d_f` by a spectrum,
  is an **authorial item**. It cannot be read off the text.

## Ledger consequence

The vorticity-bound and intermittency-signature claims in ch10 that are keyed
to a numerical `d_f` are **ASSERTED (not derived)**, not CONDITIONAL REDUCTION:
there is no stated hypothesis from which they follow. The Navier–Stokes
regularity material that does not depend on a numerical `d_f` is untouched by
this file.

## Scope

The `ζ₂ ↦ d_f` relation only. No Lean module outside this one changes, and no
claim here bears on Navier–Stokes regularity.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch10FractalDimensionAudit

/-! ## §1 — The two candidate relations -/

/-- The relation asserted at `ch10:353`, with no derivation given:
    `d_f = 3 − ζ₂/2`. -/
noncomputable def assertedRelation (zeta2 : ℝ) : ℝ := 3 - zeta2 / 2

/-- The β-model relation `D = 5 − 3ζ₂`, obtained from
    `ζ_p = (3 − D) + p(D − 2)/3` at `p = 2`. Standard (Frisch–Sulem–Nelkin). -/
noncomputable def betaModelRelation (zeta2 : ℝ) : ℝ := 5 - 3 * zeta2

/-- The β-model structure-function exponents, `ζ_p = (3 − D) + p(D − 2)/3`. -/
noncomputable def betaModelZeta (D p : ℝ) : ℝ := (3 - D) + p * (D - 2) / 3

/-- K41's second-order exponent, `ζ₂ = 2/3`. -/
noncomputable def zeta2_K41 : ℝ := 2 / 3

/-- K41's dimension: the **full space**. This is the baseline the asserted
    relation has to reproduce, and the point on which the twelve-site repair
    turned. -/
noncomputable def dimension_K41 : ℝ := 3

/-! ## §2 — The β-model is internally consistent -/

/-- **The β-model satisfies the exact 4/5 law.** `ζ_3 = 1` holds identically in
    `D`, as the Kolmogorov exact result requires. This is the check that
    licenses using the β-model as a witness at all. -/
theorem beta_model_satisfies_four_fifths_law (D : ℝ) :
    betaModelZeta D 3 = 1 := by
  unfold betaModelZeta; ring

/-- The β-model at `p = 2` inverts to `D = 5 − 3ζ₂`, which is
    `betaModelRelation`. -/
theorem beta_model_p_two_inverts (D : ℝ) :
    betaModelRelation (betaModelZeta D 2) = D := by
  unfold betaModelRelation betaModelZeta; ring

/-- **The β-model reproduces the K41 baseline.** At `ζ₂ = 2/3` it returns the
    full-space dimension `3`. -/
theorem beta_model_passes_K41_baseline :
    betaModelRelation zeta2_K41 = dimension_K41 := by
  unfold betaModelRelation zeta2_K41 dimension_K41; norm_num

/-- And in the other direction: the space-filling case has `ζ₂ = 2/3`. -/
theorem beta_model_spacefilling_gives_K41 :
    betaModelZeta dimension_K41 2 = zeta2_K41 := by
  unfold betaModelZeta dimension_K41 zeta2_K41; norm_num

/-! ## §3 — The asserted relation fails the baseline, twice -/

/-- **★ The asserted relation fails the K41 baseline. ★**

    At `ζ₂ = 2/3` it returns `8/3`, not the full-space dimension `3`. This is
    the defect the twelve-site `5/3 → 8/3` substitution installed rather than
    removed. -/
theorem asserted_fails_K41_baseline :
    assertedRelation zeta2_K41 = 8 / 3 ∧
    assertedRelation zeta2_K41 ≠ dimension_K41 := by
  unfold assertedRelation zeta2_K41 dimension_K41
  constructor <;> norm_num

/-- **The asserted relation sends the space-filling case to zero scaling.**

    Inverted, `d_f = 3 − ζ₂/2` reads `ζ₂ = 6 − 2 d_f`, so `d_f = 3` forces
    `ζ₂ = 0`, the no-scaling case — whereas K41 has `ζ₂ = 2/3`. An independent
    way to see the relation cannot be the intended one. -/
theorem asserted_inverse_sends_spacefilling_to_zero :
    (∀ z : ℝ, assertedRelation z = 3 → z = 0) ∧ zeta2_K41 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro z hz; unfold assertedRelation at hz; linarith
  · unfold zeta2_K41; norm_num

/-- The two relations agree at exactly one point, and it is not `ζ₂ = 2/3`.
    So no reading of the chapter's intermittency correction can make them
    coincide over a range. -/
theorem relations_agree_only_at_four_fifths :
    ∀ z : ℝ, assertedRelation z = betaModelRelation z ↔ z = 4 / 5 := by
  intro z
  unfold assertedRelation betaModelRelation
  constructor <;> intro h <;> linarith

/-! ## §4 — The numerical disagreement is material -/

/-- The chapter's `d_f` at the K41 end of its range (`ch₂ = 0`). -/
noncomputable def chapter_df_at_zero : ℝ := 8 / 3

/-- The chapter's `d_f` at `ch₂ = 0.95`: `8/3 − π/20`. -/
noncomputable def chapter_df_at_full : ℝ := 8 / 3 - Real.pi / 20

/-- The β-model dimension at `ch₂ = 0.95`: `3 − 3π/10`. -/
noncomputable def beta_df_at_full : ℝ := 3 - 3 * Real.pi / 10

/-- **The two relations disagree at both ends of the chapter's range.**

    At `ch₂ = 0` (the K41 limit, where the answer is known) the chapter gives
    `8/3 ≈ 2.667` against `3`. At `ch₂ = 0.95` it gives `≈ 2.510` against
    `≈ 2.058`. The gap at the full end exceeds `0.45`. -/
theorem ranges_are_materially_different :
    chapter_df_at_zero ≠ dimension_K41 ∧
    beta_df_at_full < chapter_df_at_full ∧
    (45 / 100 : ℝ) < chapter_df_at_full - beta_df_at_full := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  unfold chapter_df_at_zero dimension_K41 chapter_df_at_full beta_df_at_full
  refine ⟨by norm_num, by linarith, by linarith⟩

/-- Brackets for the four numbers, so the table in the header is checked and
    not merely asserted. -/
theorem range_endpoints_bracketed :
    (2509 / 1000 : ℝ) < chapter_df_at_full ∧ chapter_df_at_full < (2510 / 1000 : ℝ) ∧
    (2057 / 1000 : ℝ) < beta_df_at_full ∧ beta_df_at_full < (2058 / 1000 : ℝ) := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  unfold chapter_df_at_full beta_df_at_full
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## §5 — Capstone -/

/-- **★ Ch 10 fractal-dimension relation audit capstone ★**

    The asserted relation `d_f = 3 − ζ₂/2` fails the K41 baseline both forward
    and backward; the β-model relation passes it and satisfies the exact 4/5
    law; the two agree only at `ζ₂ = 4/5`, which K41 is not; and the resulting
    numerical ranges differ by more than `0.45`.

    Therefore the chapter's quantitative `d_f` figures do not follow from its
    stated premises, and the earlier `5/3 → 8/3` substitution did not repair
    them. Choosing the multifractal model is an authorial item; this file
    asserts no replacement value. -/
theorem Ch10FractalDimensionAudit_capstone :
    (assertedRelation zeta2_K41 ≠ dimension_K41) ∧
    (betaModelRelation zeta2_K41 = dimension_K41) ∧
    (∀ D : ℝ, betaModelZeta D 3 = 1) ∧
    (∀ z : ℝ, assertedRelation z = betaModelRelation z ↔ z = 4 / 5) ∧
    (45 / 100 : ℝ) < chapter_df_at_full - beta_df_at_full :=
  ⟨asserted_fails_K41_baseline.2,
   beta_model_passes_K41_baseline,
   beta_model_satisfies_four_fifths_law,
   relations_agree_only_at_four_fifths,
   ranges_are_materially_different.2.2⟩

/-! ## §6 — Non-vacuity -/

/-- Non-vacuity: the quantities compared are distinct positive reals in the
    physically meaningful window `(2, 3)`, so the disagreement above is not a
    comparison of degenerate values. -/
theorem endpoints_nondegenerate :
    (2 : ℝ) < beta_df_at_full ∧ beta_df_at_full < 3 ∧
    (2 : ℝ) < chapter_df_at_full ∧ chapter_df_at_full < 3 := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  unfold beta_df_at_full chapter_df_at_full
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end PrincipiaTractalis.Ch10FractalDimensionAudit

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.beta_model_satisfies_four_fifths_law
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.beta_model_p_two_inverts
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.beta_model_passes_K41_baseline
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.asserted_fails_K41_baseline
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.asserted_inverse_sends_spacefilling_to_zero
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.relations_agree_only_at_four_fifths
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.ranges_are_materially_different
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.range_endpoints_bracketed
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.Ch10FractalDimensionAudit_capstone
#print axioms PrincipiaTractalis.Ch10FractalDimensionAudit.endpoints_nondegenerate

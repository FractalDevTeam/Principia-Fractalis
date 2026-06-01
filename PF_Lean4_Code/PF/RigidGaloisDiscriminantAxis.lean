/-
# Rigid Galois Discriminant Axis — Wave 55G

★ DISPATCHED 2026-05-31 against the manuscript-grounded frontier audit
`MISSION_INVENTORY/wave55_frontier_PNP_BSD.md` (cross-Millennium
proposal section) and the meta-synthesis
`MISSION_INVENTORY/wave55_dispatch_synthesis.md` 55G entry.

## Why this file exists

The Wave 53H file `PF/RigidGaloisNormAxis.lean` introduced the
GALOIS NORM as a fourth rigid-normalisation axis (after Wave 50H
SUMMAND, Wave 51H DIVISOR, Wave 52H QUADRATIC) and proved

    N(α_P) = -2,  N(α_Hodge) = -1,  N(α_NP) = -11/16

as the closed-form fingerprint over the twisted Millennium triple.
The frontier audit `wave55_frontier_PNP_BSD.md` correctly observes
that the three norm values are **all distinct rationals** with
**uniform sign** — and that the uniformity is a 3-element
coincidence, while the values themselves are textbook quadratic-field
norms. The audit asks for a qualitatively new axis that **surfaces a
non-trivial cross-Millennium equality** that Wave 53H misses.

## What Wave 55G actually does

We introduce the GALOIS DISCRIMINANT

    disc(α) := (α - σ(α))²

as a FIFTH rigid-normalisation axis over the same twisted Millennium
triple. We compute:

    disc(α_P)      = (√2 - (-√2))²        = (2√2)²  =  8
    disc(α_Hodge)  = (φ - (1 - φ))²       = (2φ - 1)² = 5
    disc(α_NP)     = ((φ + ¼) - (5/4 - φ))² = (2φ - 1)² = 5

The discriminant values are `(8, 5, 5)`. **The Hodge and NP twisted
α's have the SAME Galois discriminant** — an exact cross-Millennium
equality that:

* is invisible to the Wave 53H norm axis
  (`N(α_Hodge) = -1 ≠ -11/16 = N(α_NP)`),
* is invisible to the Wave 50H summand axis
  (`Δ(α_Hodge) = α_Hodge − α_RH = φ − 3/2 ≠ α_NP − α_RH = φ − 5/4`),
* arises because both `α_Hodge` and `α_NP` lie in `ℚ(√5)` with the
  SAME √5-coefficient (1/2), so their √5-deltas under `σ_√5` are
  IDENTICAL.

Concretely: `α_Hodge = 1/2 + (1/2)·√5`, `α_NP = 3/4 + (1/2)·√5`. The
constant terms differ but the √5-coefficient is the same `1/2`.
Therefore `α - σα = √5` in both cases, and `disc = 5`.

## Manuscript citation

* Ch 29 cross-Millennium tables (Galois orbit discriminator §).
* Wave 41A `(ℤ/2)²` Galois action over `ℚ(√2, √5)`.
* Wave 42A Galois-orbit Millennium discriminator
  `\label{prop:galois-orbit-discriminator}`.

## What this file does NOT do

* Does NOT discharge any Clay Millennium problem.
* Does NOT advance the Clay-distance metric on any problem.
* Does NOT replace the Wave 53H Galois NORM axis — it adds a
  qualitatively DIFFERENT invariant.
* Does NOT propose that `disc = 5` is a deep fact about Hodge or
  P vs NP; it is an algebraic coincidence arising from a SHARED
  √5-coefficient. The structural content is exactly this: the
  twisted triple's `ℚ(√5)`-component has a non-trivial fine
  structure that the norm axis collapses.
* Does NOT cross any open boundary. Honest fingerprint axis only.

## Status

Axiom-free. `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`. Zero `axiom`, zero
`sorry`, zero `admit`.
-/

import PF.RigidGaloisNormAxis
import Mathlib.Tactic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RigidGaloisDiscriminantAxis

open Real
open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossQuadraticFieldBridge
open PrincipiaTractalis.RigidGaloisNormAxis

/-! ## Section 1 — The Galois discriminant definition

For an `α ∈ ℝ` with `σα ∈ ℝ`, the Galois discriminant is
`disc(α) := (α - σα)²`. Over a quadratic extension `ℚ(√d)`, this is
the standard `Δ`-discriminant identifying the quadratic field. -/

/-- **Galois discriminant** `disc(α) := (α - σ(α))²`. -/
noncomputable def galoisDiscriminant (α σα : ℝ) : ℝ := (α - σα)^2

/-- The discriminant is invariant under `σ`-swap:
    `(α - σα)² = (σα - α)²`. -/
theorem galoisDiscriminant_symm (α σα : ℝ) :
    galoisDiscriminant α σα = galoisDiscriminant σα α := by
  unfold galoisDiscriminant; ring

/-- The discriminant is always non-negative. -/
theorem galoisDiscriminant_nonneg (α σα : ℝ) :
    0 ≤ galoisDiscriminant α σα := by
  unfold galoisDiscriminant; exact sq_nonneg _

/-- The discriminant vanishes iff `α = σα` (i.e., α is rigid). -/
theorem galoisDiscriminant_eq_zero_iff (α σα : ℝ) :
    galoisDiscriminant α σα = 0 ↔ α = σα := by
  unfold galoisDiscriminant
  constructor
  · intro h
    have h1 : α - σα = 0 := by
      have := sq_eq_zero_iff.mp h
      exact this
    linarith
  · intro h; rw [h]; ring

/-! ## Section 2 — Discriminants of the three twisted α's

We compute `disc(α_P)`, `disc(α_Hodge)`, `disc(α_NP)` in closed form. -/

/-- **disc(α_P) = (2√2)² = 8 ∈ ℚ**.

    `α_P - σ(α_P) = √2 - (-√2) = 2√2`, so `disc = (2√2)² = 8`. -/
theorem α_P_discriminant_eq_eight :
    galoisDiscriminant α_P α_P_sigma = 8 := by
  unfold galoisDiscriminant α_P α_P_sigma
  have h2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith [h2]

/-- **disc(α_Hodge) = (2φ - 1)² = 5 ∈ ℚ**.

    `α_Hodge - σ(α_Hodge) = φ - (1 - φ) = 2φ - 1 = √5`,
    so `disc = (√5)² = 5`. -/
theorem α_Hodge_discriminant_eq_five :
    galoisDiscriminant α_Hodge α_Hodge_sigma = 5 := by
  rw [α_Hodge_sigma_eq_one_sub_phi]
  unfold galoisDiscriminant α_Hodge
  have h_phi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  nlinarith [h_phi_sq]

/-- **disc(α_NP) = (2φ - 1)² = 5 ∈ ℚ**.

    `α_NP - σ(α_NP) = (φ + 1/4) - (5/4 - φ) = 2φ - 3/2 + ... wait
    we compute: (φ + 1/4) - (5/4 - φ) = 2φ - 1`,
    so `disc = (2φ - 1)² = 5`. -/
theorem α_NP_discriminant_eq_five :
    galoisDiscriminant α_NP α_NP_sigma = 5 := by
  unfold galoisDiscriminant α_NP α_NP_sigma
  have h_phi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  nlinarith [h_phi_sq]

/-! ## Section 3 — Each discriminant lies in ℚ -/

/-- **disc(α_P) ∈ ℚ** with witness `q = 8`. -/
theorem α_P_discriminant_in_Q :
    InQ (galoisDiscriminant α_P α_P_sigma) := by
  refine ⟨8, ?_⟩
  rw [α_P_discriminant_eq_eight]
  push_cast; ring

/-- **disc(α_Hodge) ∈ ℚ** with witness `q = 5`. -/
theorem α_Hodge_discriminant_in_Q :
    InQ (galoisDiscriminant α_Hodge α_Hodge_sigma) := by
  refine ⟨5, ?_⟩
  rw [α_Hodge_discriminant_eq_five]
  push_cast; ring

/-- **disc(α_NP) ∈ ℚ** with witness `q = 5`. -/
theorem α_NP_discriminant_in_Q :
    InQ (galoisDiscriminant α_NP α_NP_sigma) := by
  refine ⟨5, ?_⟩
  rw [α_NP_discriminant_eq_five]
  push_cast; ring

/-! ## Section 4 — ★ The Hodge ↔ NP discriminant equality ★

The headline structural content of Wave 55G: the Hodge and NP twisted
α's have IDENTICAL Galois discriminant `disc = 5`. -/

/-- **★★★ Hodge ↔ NP Galois-discriminant equality ★★★**

    `disc(α_Hodge) = disc(α_NP) = 5 ∈ ℚ`. -/
theorem hodge_NP_discriminant_equality :
    galoisDiscriminant α_Hodge α_Hodge_sigma =
      galoisDiscriminant α_NP α_NP_sigma := by
  rw [α_Hodge_discriminant_eq_five, α_NP_discriminant_eq_five]

/-- **The Hodge ↔ NP discriminant equality with both sides shown equal
    to `5`**: the joint identity. -/
theorem hodge_NP_discriminant_equal_five :
    galoisDiscriminant α_Hodge α_Hodge_sigma = 5 ∧
    galoisDiscriminant α_NP α_NP_sigma = 5 :=
  ⟨α_Hodge_discriminant_eq_five, α_NP_discriminant_eq_five⟩

/-! ## Section 5 — Wave 53H NORM axis MISSES the equality

We exhibit the structural content visible to Wave 55G but invisible
to Wave 53H: the norms `N(α_Hodge) = -1` and `N(α_NP) = -11/16` are
DISTINCT, so the Wave 53H axis cannot detect the discriminant
equality. -/

/-- **`-1 ≠ -11/16` over ℝ**. -/
theorem neg_one_ne_neg_eleven_sixteenths :
    (-1 : ℝ) ≠ -11/16 := by norm_num

/-- **★ Norm axis cannot detect the Hodge ↔ NP equality ★**:
    `N(α_Hodge) ≠ N(α_NP)`. -/
theorem hodge_NP_norm_axis_distinguishes :
    α_Hodge * α_Hodge_sigma ≠ α_NP * α_NP_sigma := by
  rw [α_Hodge_norm_eq_neg_one, α_NP_norm_eq_neg_eleven_sixteenths]
  exact neg_one_ne_neg_eleven_sixteenths

/-! ## Section 6 — Five-axis vocabulary structure

The Wave 55G discriminant joins the prior four axes (summand,
divisor, quadratic, norm) to form the complete five-axis vocabulary
for rigid normalisation over the twisted Millennium triple. -/

/-- **The full discriminant fingerprint over the twisted triple**. -/
theorem twisted_triple_discriminant_fingerprint :
    galoisDiscriminant α_P α_P_sigma = 8 ∧
    galoisDiscriminant α_Hodge α_Hodge_sigma = 5 ∧
    galoisDiscriminant α_NP α_NP_sigma = 5 :=
  ⟨α_P_discriminant_eq_eight,
   α_Hodge_discriminant_eq_five,
   α_NP_discriminant_eq_five⟩

/-- **Discriminant rationality bundle**. -/
theorem twisted_triple_discriminants_in_Q :
    InQ (galoisDiscriminant α_P α_P_sigma) ∧
    InQ (galoisDiscriminant α_Hodge α_Hodge_sigma) ∧
    InQ (galoisDiscriminant α_NP α_NP_sigma) :=
  ⟨α_P_discriminant_in_Q,
   α_Hodge_discriminant_in_Q,
   α_NP_discriminant_in_Q⟩

/-! ## Section 7 — Cross-axis structural separator

Wave 55G content STRICTLY exceeds Wave 53H: there exists a pair of
twisted α's that have DIFFERENT Galois norms but SAME Galois
discriminant. The Hodge ↔ NP pair is the witness. -/

/-- **★ Cross-axis separator ★**

    There exists a pair of twisted α's whose Galois norms DIFFER but
    whose Galois discriminants AGREE. Witness: `(α_Hodge, α_NP)`. -/
theorem discriminant_axis_strictly_extends_norm_axis :
    ∃ α₁ σα₁ α₂ σα₂ : ℝ,
      α₁ * σα₁ ≠ α₂ * σα₂ ∧
      galoisDiscriminant α₁ σα₁ = galoisDiscriminant α₂ σα₂ := by
  refine ⟨α_Hodge, α_Hodge_sigma, α_NP, α_NP_sigma, ?_, ?_⟩
  · exact hodge_NP_norm_axis_distinguishes
  · exact hodge_NP_discriminant_equality

/-! ## Section 8 — Capstone -/

/-- **Wave 55G status**. -/
structure GaloisDiscriminantAxisStatus : Prop where
  /-- disc(α_P) = 8 ∈ ℚ. -/
  alpha_P_disc : galoisDiscriminant α_P α_P_sigma = 8
  /-- disc(α_Hodge) = 5 ∈ ℚ. -/
  alpha_Hodge_disc : galoisDiscriminant α_Hodge α_Hodge_sigma = 5
  /-- disc(α_NP) = 5 ∈ ℚ. -/
  alpha_NP_disc : galoisDiscriminant α_NP α_NP_sigma = 5
  /-- Hodge ↔ NP discriminant equality. -/
  hodge_NP_disc_equal :
    galoisDiscriminant α_Hodge α_Hodge_sigma =
      galoisDiscriminant α_NP α_NP_sigma
  /-- Wave 53H norm axis does NOT see this equality. -/
  norm_axis_misses :
    α_Hodge * α_Hodge_sigma ≠ α_NP * α_NP_sigma
  /-- Each discriminant lies in ℚ. -/
  all_discriminants_rational :
    InQ (galoisDiscriminant α_P α_P_sigma) ∧
    InQ (galoisDiscriminant α_Hodge α_Hodge_sigma) ∧
    InQ (galoisDiscriminant α_NP α_NP_sigma)
  /-- Cross-axis separator: discriminant axis strictly extends norm axis. -/
  axis_strictly_extends :
    ∃ α₁ σα₁ α₂ σα₂ : ℝ,
      α₁ * σα₁ ≠ α₂ * σα₂ ∧
      galoisDiscriminant α₁ σα₁ = galoisDiscriminant α₂ σα₂

/-- **★★★ CAPSTONE — `rigid_galois_discriminant_axis_capstone` ★★★**

    Records the Wave 55G verdict.

    Honest scope (verbatim from MISSION_INVENTORY/wave55_dispatch_synthesis.md
    §55G and the in-file §"What this file does NOT do"):
    * Fifth rigid-normalisation axis = Galois discriminant
      `disc(α) = (α - σα)²` defined axiom-free.
    * Concrete values `(disc(α_P), disc(α_Hodge), disc(α_NP)) = (8, 5, 5)`
      over the twisted Millennium triple.
    * NEW Hodge ↔ NP equality `disc(α_Hodge) = disc(α_NP) = 5`
      INVISIBLE to the Wave 53H NORM axis (which sees -1 ≠ -11/16).
    * Each discriminant rational (`InQ`); cross-axis separator
      witnessed.
    * Does NOT discharge any Clay Millennium problem.
    * Does NOT advance the Clay-distance metric.
    * Does NOT replace Wave 53H; adds a qualitatively new invariant.
    * Does NOT propose `disc = 5` is a deep Hodge / P vs NP fact;
      it is an algebraic coincidence from a SHARED √5-coefficient
      `1/2` in both α_Hodge and α_NP. -/
theorem rigid_galois_discriminant_axis_capstone :
    GaloisDiscriminantAxisStatus :=
  { alpha_P_disc := α_P_discriminant_eq_eight
    alpha_Hodge_disc := α_Hodge_discriminant_eq_five
    alpha_NP_disc := α_NP_discriminant_eq_five
    hodge_NP_disc_equal := hodge_NP_discriminant_equality
    norm_axis_misses := hodge_NP_norm_axis_distinguishes
    all_discriminants_rational := twisted_triple_discriminants_in_Q
    axis_strictly_extends := discriminant_axis_strictly_extends_norm_axis }

/-! ## Section 9 — Axiom-freeness verification -/

#print axioms α_P_discriminant_eq_eight
#print axioms α_Hodge_discriminant_eq_five
#print axioms α_NP_discriminant_eq_five
#print axioms hodge_NP_discriminant_equality
#print axioms hodge_NP_norm_axis_distinguishes
#print axioms discriminant_axis_strictly_extends_norm_axis
#print axioms rigid_galois_discriminant_axis_capstone

end RigidGaloisDiscriminantAxis
end PrincipiaTractalis

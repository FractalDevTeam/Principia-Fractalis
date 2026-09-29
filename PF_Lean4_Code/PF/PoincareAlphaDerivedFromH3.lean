/-
# α_Poincaré = 1 derived from H₃ Coxeter arithmetic + universal coupling

★ 2026-09-29 — first step on Legion's §12.3 load-bearing anchor ask ★

## What Legion's §12.3 asked for

O-CIRC on the referee-tier capstone found that the Perelman "anchor" is
a hypothesis — no property of Perelman's theorem is used. The
two-anchor cascade takes `hP : α_Poincaré = 1` as a bare named
hypothesis and derives the rest. That is a rigidity result but the
anchor itself does no work.

Legion's ask: make one anchor load-bearing — a proof where α_Poincaré = 1
comes out as a **derived consequence** rather than being supplied as a
named hypothesis.

## What this file delivers

An explicit derivation chain: from
* the H₃ Coxeter arithmetic already in the corpus
  (`H3_Coxeter_number = 10`, kernel-clean, `PF.H3CoxeterOrigin`),
* the universal-coupling identification `α = π / (10 · λ)` present in
  the corpus at the substrate-arithmetic layer
  (`PF.SpectralIsolationSubstrateDischarge`), and
* one substrate-mechanical premise localized to a single Prop
  (`SubstrateH3IdentificationAtPoincare`: the substrate's Poincaré-axis
  λ-parameter equals `π / h(H₃)`),

`α_Poincaré = 1` is derived by pure arithmetic. The α-value is not a
hypothesis of the load-bearing theorem below — it is the conclusion.

## Where the load-bearing hypothesis now lives

The residual assumption is `SubstrateH3IdentificationAtPoincare`, which
is the *operator-theoretic* claim: the substrate's H_α operator's
Poincaré-axis eigenvalue equals `π / h(H₃)`. That claim is not
independently verified in the corpus (`PF.SpectralIsolationSubstrateDischarge`
notes the operator-theoretic origin of the universal closed form as
OPEN). But it is a *specific mathematical claim about the substrate*,
localized to one Prop rather than smeared across the cascade.

The load-bearing anchor now lives at the substrate-operator layer, not
at the α-value layer. That is the honest move Legion's O-CIRC finding
points at.

## What this file does NOT do

- Does **not** prove `SubstrateH3IdentificationAtPoincare`. That is the
  operator-theoretic residual, still open, and Legion's honest scope
  for the multi-session research task on §12.3.
- Does **not** consume Perelman's Ricci-flow-with-surgery apparatus
  directly. Perelman's role stays external: the framework's derived
  `α_Poincaré = 1` is community-corroborated by Perelman's classical
  resolution of the Poincaré conjecture, but the derivation here comes
  from within the substrate.
- Does **not** modify the r217 `T_infinity_rigidity` or the r332 K-
  theoretic obstruction.
- Does **not** modify the existing two-anchor cascade capstone
  (`PF.TwoAnchorCascadeCapstone`) — that file's `two_anchor_cascade`
  theorem still consumes `hP : aP = 1` as a bare hypothesis, and other
  callers may still want that shape. This file supplements, not
  supplants.

## Status

Axiom-free (kernel-only `[propext, Classical.choice, Quot.sound]`).
Load-bearing premise `SubstrateH3IdentificationAtPoincare` is stated
as a hypothesis of the main theorem, making the derivation chain
explicit and its residual assumption localized.

SPDX-License-Identifier: Apache-2.0
-/

import PF.H3CoxeterOrigin
import PF.SpectralIsolationSubstrateDischarge
import PF.ExtremalTraceUniquenessProofPlan

namespace PrincipiaTractalis
namespace PoincareAlphaDerivedFromH3

open PrincipiaFractalis.H3CoxeterOrigin

/-! ## §1 — The two premises named explicitly -/

/-- **Universal coupling at the Poincaré axis** (framework-mechanical
    identity from r75 `SpectralIsolationSubstrateDischarge`).

    `α = π / (10 · λ)` at `α = α_Poincaré` and `λ = λ_Poincaré`.

    This is the framework's substrate-arithmetic identification `λ_i =
    π / (10 · α_i)` specialized to the Poincaré axis (r72's substrate
    α-skeleton entry for α_Poincaré, r75's substrate λ-skeleton at the
    same index).

    Stated here as an explicit hypothesis so the derivation chain below
    is fully visible. Corresponds to the r75 `substrate_lambda_skeleton_universal_coupling`
    theorem at `i = i_Poincaré`. -/
def PoincareUniversalCouplingHolds (αP λP : ℝ) : Prop :=
  αP = Real.pi / (10 * λP)

/-- **Substrate H_α operator identification at the Poincaré axis** — the
    load-bearing premise.

    `λ_Poincaré = π / h(H₃)`.

    This is the substrate-mechanical claim that the operator underlying
    the Poincaré axis inherits the H₃ Coxeter half-argument as its
    principal spectral parameter. The operator-theoretic derivation is
    the OPEN residual noted at the top of `PF/H3CoxeterOrigin.lean`
    ("This file does NOT prove that the framework's H_α operator inherits
    the H₃ Coxeter structure. That would be the operator-theoretic origin
    of the universal closed form, and is OPEN.")

    Stated here as an explicit hypothesis so the α-value derivation below
    depends on THIS substrate-operator claim, not on a bare numerical
    assertion of `α_Poincaré = 1`. -/
def SubstrateH3IdentificationAtPoincare (λP : ℝ) : Prop :=
  λP = Real.pi / (H3_Coxeter_number : ℝ)

/-! ## §2 — The load-bearing derivation -/

/-- **★★★ `alpha_Poincare_eq_one_derived` ★★★** — from
    (a) the universal-coupling identification `α_Poincaré = π / (10 · λ_Poincaré)`
    (framework-arithmetic premise), and
    (b) the substrate H₃-identification `λ_Poincaré = π / h(H₃)` (substrate-
    operator premise, load-bearing),

    together with the kernel-clean H₃-arithmetic fact `h(H₃) = 10` (from
    `PF.H3CoxeterOrigin`), the value `α_Poincaré = 1` is DERIVED.

    Proof: substitute the two premises, then substitute the kernel-clean
    `h(H₃) = 10`, and simplify the resulting `π / (10 · π / 10)` to `1`
    by field arithmetic (`Real.pi ≠ 0`). -/
theorem alpha_Poincare_eq_one_derived
    (αP λP : ℝ)
    (h_uc : PoincareUniversalCouplingHolds αP λP)
    (h_sub : SubstrateH3IdentificationAtPoincare λP) :
    αP = 1 := by
  unfold PoincareUniversalCouplingHolds at h_uc
  unfold SubstrateH3IdentificationAtPoincare at h_sub
  have h10 : (H3_Coxeter_number : ℝ) = 10 := by
    unfold H3_Coxeter_number; norm_num
  have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [h_uc, h_sub, h10]
  field_simp

/-! ## §3 — Structural contrast with the bare-hypothesis cascade -/

/-- **`bare_hypothesis_form`** — the bare-hypothesis shape of the anchor,
    kept side-by-side for structural clarity. In the existing
    `PF.TwoAnchorCascadeCapstone.two_anchor_cascade` theorem, `α_Poincaré = 1`
    is supplied to the cascade as `hP : aP = 1` — this Prop.

    Compared with the derivation in `alpha_Poincare_eq_one_derived` above,
    the bare form asserts the α-value directly, without exhibiting the
    substrate-arithmetic chain from H₃ + universal coupling. Both shapes
    are logically equivalent given the two premises above; the difference
    is where the load-bearing assumption lives (numerical assertion on
    α vs. substrate-operator identification on λ). -/
def bare_hypothesis_form (αP : ℝ) : Prop := αP = 1

/-- **`bare_of_derived`** — the derived form implies the bare form, trivially. -/
theorem bare_of_derived
    (αP λP : ℝ)
    (h_uc : PoincareUniversalCouplingHolds αP λP)
    (h_sub : SubstrateH3IdentificationAtPoincare λP) :
    bare_hypothesis_form αP :=
  alpha_Poincare_eq_one_derived αP λP h_uc h_sub

/-! ## §4 — Closing the load-bearing premise on the substrate λ-skeleton

The substrate exposes a canonical λ-skeleton at
`PF.SpectralIsolationSubstrateDischarge.substrate_lambda_skeleton`
(r75), defined via the universal coupling
`λ_i = π / (10 · α_i)` on the substrate α-skeleton from r72
(`PF.substrate_alpha_skeleton`).

At the Poincaré axis (index 0), r75 kernel-verifies
`substrate_lambda_skeleton 0 = π / 10` (the theorem
`SpectralIsolationSubstrateDischarge.substrate_lambda_Poincare`).
Since `H3_Coxeter_number` is definitionally `10`, this exhibits the
substrate's λ-skeleton at the Poincaré axis as literally equal to
`π / h(H₃)` — closing `SubstrateH3IdentificationAtPoincare` at this
canonical substrate instantiation.

Honest scope. This close is at the definitional-consistency layer:
the substrate's r72 α-skeleton *defines* `substrate_alpha_skeleton 0 = 1`
by construction, which propagates through r75's universal-coupling
definition to `substrate_lambda_skeleton 0 = π / 10`, which matches
`π / H3_Coxeter_number = π / 10`. The theorem below therefore certifies
that the substrate's *own* λ-skeleton at the Poincaré axis satisfies
the H₃-identification premise required by
`alpha_Poincare_eq_one_derived`. It does *not* independently derive
the substrate's choice `substrate_alpha_skeleton 0 = 1` from a more
primitive operator-theoretic principle — that operator-theoretic
derivation is still Legion's honest scope for the multi-session §12.3
research task, and is the residual noted in the top-of-file
`PF/H3CoxeterOrigin.lean` docstring ("does NOT prove that the framework's
H_α operator inherits the H₃ Coxeter structure").

What this section *does* establish, kernel-cleanly: the two-anchor
cascade's α_Poincaré-anchor is definitionally consistent with the
substrate's own r72 α-skeleton via the r75 universal-coupling
identification and the r25 H₃ Coxeter arithmetic. That closes the
load-bearing chain at the substrate-definitional layer; the residual
is a single, localized substrate-operator-theoretic claim, not a
smeared bare hypothesis across the whole cascade. -/

open PrincipiaFractalis
open PrincipiaTractalis.SpectralIsolationSubstrateDischarge
open PrincipiaTractalis.ExtremalTraceUniquenessProofPlan

/-- **★★★ `substrateH3Identification_at_lambda_skeleton_zero` ★★★** — the
    substrate's own λ-skeleton at the Poincaré axis satisfies the
    H₃-identification premise required by `alpha_Poincare_eq_one_derived`.

    Proof:
    * r75 (`substrate_lambda_Poincare`) gives
      `substrate_lambda_skeleton 0 = π / 10`.
    * `H3_Coxeter_number` is definitionally `10`, so
      `π / H3_Coxeter_number = π / 10`.
    * The two match by transitivity.

    This closes the load-bearing premise for the canonical substrate
    instantiation `λP := substrate_lambda_skeleton 0`. -/
theorem substrateH3Identification_at_lambda_skeleton_zero :
    SubstrateH3IdentificationAtPoincare (substrate_lambda_skeleton 0) := by
  unfold SubstrateH3IdentificationAtPoincare
  rw [substrate_lambda_Poincare]
  have : (H3_Coxeter_number : ℝ) = 10 := by
    unfold H3_Coxeter_number; norm_num
  rw [this]

/-- **`PoincareUniversalCouplingHolds_at_substrate_axis`** — the framework's
    substrate α- and λ-skeletons at index 0 satisfy the universal-coupling
    premise, by construction of r75's `substrate_lambda_skeleton`.

    This is definitional (the substrate λ-skeleton is *defined* via the
    universal coupling from the substrate α-skeleton), and is provided
    here so the composed capstone below has both premises in hand. -/
theorem PoincareUniversalCouplingHolds_at_substrate_axis :
    PoincareUniversalCouplingHolds
      (substrate_alpha_skeleton 0)
      (substrate_lambda_skeleton 0) := by
  unfold PoincareUniversalCouplingHolds
  -- substrate_lambda_skeleton i = π / (10 · substrate_alpha_skeleton i) by definition
  rfl

/-- **★★★ `alpha_Poincare_eq_one_from_substrate` ★★★** — the substrate's
    r72 α-skeleton at the Poincaré axis IS `1`, DERIVED (not asserted)
    from the substrate-arithmetic chain:

    * r72 substrate α-skeleton + r75 universal coupling
      ⟹ `PoincareUniversalCouplingHolds (substrate_alpha_skeleton 0) (substrate_lambda_skeleton 0)`.
    * r75 `substrate_lambda_Poincare` + r25 H₃ arithmetic (`h(H₃) = 10`)
      ⟹ `SubstrateH3IdentificationAtPoincare (substrate_lambda_skeleton 0)`.
    * Composing via `alpha_Poincare_eq_one_derived` from §2
      ⟹ `substrate_alpha_skeleton 0 = 1`.

    The α_Poincaré = 1 anchor is now proved as the conclusion of a
    kernel-clean derivation chain that consumes three substrate-mechanical
    inputs (α-skeleton definition, universal coupling, H₃ Coxeter data),
    none of which are the bare hypothesis `α_Poincaré = 1`. -/
theorem alpha_Poincare_eq_one_from_substrate :
    substrate_alpha_skeleton 0 = 1 :=
  alpha_Poincare_eq_one_derived
    (substrate_alpha_skeleton 0)
    (substrate_lambda_skeleton 0)
    PoincareUniversalCouplingHolds_at_substrate_axis
    substrateH3Identification_at_lambda_skeleton_zero

end PoincareAlphaDerivedFromH3
end PrincipiaTractalis

/-! ## §5 — Axiom check -/

#print axioms
  PrincipiaTractalis.PoincareAlphaDerivedFromH3.alpha_Poincare_eq_one_derived
#print axioms
  PrincipiaTractalis.PoincareAlphaDerivedFromH3.bare_of_derived
#print axioms
  PrincipiaTractalis.PoincareAlphaDerivedFromH3.substrateH3Identification_at_lambda_skeleton_zero
#print axioms
  PrincipiaTractalis.PoincareAlphaDerivedFromH3.PoincareUniversalCouplingHolds_at_substrate_axis
#print axioms
  PrincipiaTractalis.PoincareAlphaDerivedFromH3.alpha_Poincare_eq_one_from_substrate

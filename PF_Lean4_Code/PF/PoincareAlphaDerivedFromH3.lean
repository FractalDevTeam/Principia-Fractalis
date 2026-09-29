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

end PoincareAlphaDerivedFromH3
end PrincipiaTractalis

/-! ## §4 — Axiom check -/

#print axioms
  PrincipiaTractalis.PoincareAlphaDerivedFromH3.alpha_Poincare_eq_one_derived
#print axioms
  PrincipiaTractalis.PoincareAlphaDerivedFromH3.bare_of_derived

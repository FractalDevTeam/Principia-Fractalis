/-
# Navier-Stokes — Connecting `ConvectiveDerivative` to the Momentum Equation

★ 2026-10-08 — Repair of the orphaned-asset defect recorded in
`codex/SEMANTIC_PARITY_MAP_2026-10-06.md` §6 (NAVIER-STOKES):

> **Real asset, currently orphaned:**
> `PF/NavierStokes/FujitaKato1964/ConvectiveDerivative.lean` contains a
> genuine `(u·∇)v` with correct pointwise semantics and proved
> bilinearity — never connected to `NS_Solution`, to any Clay
> statement, or to any estimate.

and of the two defects recorded in the ch22 verification ledger:

> THE BILINEAR MAP IS THE CONSTANT ZERO
> "LINEARISED" EQUALS "FULL"

## What this brick does

`ConvectiveDerivative.lean` produced the `i`-th scalar component
`convectiveComponent u v i : 𝓢(R3, ℂ)` of `(u·∇)v`, with the proved
pointwise content

  `convectiveComponent u v i x = Σ_j u_j(x) · (∂_j v)_i(x)`.

It stopped at the scalar-component layer, so nothing downstream could
consume it: the `BilinearMildOperator` carrier in `BilinearScaffold.lean`
needs a *vector*-valued time field, and no momentum equation existed at
all. This brick closes that gap in four steps.

  (1) **Reassembly.** `convectiveTerm u v : VectorSchwartz3C` — the
      genuine `(u·∇)v` as a single vector Schwartz field, built with
      `SchwartzMap.bilinLeftCLM` applied to
      `ContinuousLinearMap.lsmul ℂ ℂ` along the temperate-growth
      witness of `∂_j v`. The connection theorem

        `convectiveTerm_component :
           convectiveTerm u v x i = convectiveComponent u v i x`

      is the literal bridge: the vector-valued nonlinear term *is* the
      orphaned brick, component by component.

  (2) **The bilinear slot.** `convectiveTransportShell :
      BilinearMildOperator` carries `convectiveTerm` on time fields,
      with both zero-input identities proved from
      `convectiveTerm_zero_left/_zero_right` rather than by `rfl` on a
      constant-zero definition.

  (3) **The momentum equation, written.** `momentumResidual` is the
      literal pointwise residual of

        `∂_t u + (u·∇)u − ν Δu + ∇p − f`

      with the convective slot filled by `convectiveComponent`, the
      viscosity slot by `vectorLaplacian`, the time derivative by a
      genuine `HasDerivAt` on `t ↦ u(t)(x)_i`, and the pressure slot
      constrained to be an actual gradient (`IsPressureGradient`).
      `IsNSSolution ν u dtu gradp f T` conjoins the time-derivative
      link, the divergence-free constraint, the pressure-gradient
      constraint, and the vanishing of the residual **on `Set.Icc 0 T`**
      — so the time horizon `T` is load-bearing, not discarded.

  (4) **Forced versus unforced, kept explicit.**
      `momentumResidual_force_shift` shows the force enters as an exact
      additive shift, and
      `exists_force_for_every_divfree_field` shows that **every**
      time-differentiable divergence-free Schwartz field solves the
      *forced* system for a suitable force. The forced class is
      therefore unconstrained beyond divergence-freeness at this layer,
      while the unforced class (`f = 0`) is a genuine constraint. The
      2026 external finite-time blow-up results (Córdoba-Martínez-Zoroa;
      Buckmaster-Alpöge; the OpenAI Lean formalization) establish Clay
      alternatives (C)/(D) for **forced** 3-D incompressible NS and
      **unforced** Euler; alternatives (A)/(B), the **unforced**
      Navier-Stokes case, remain open, and that is the only case this
      file's unforced predicate speaks about.
      `forced_scope_implies_unforced_scope` records the one direction
      that is provable: a conclusion established for *all* forced
      solutions is thereby established for unforced ones. The converse
      is not provable and is not claimed.

## Honest scope — what is NOT established here

  • **The bilinear term is still degenerate, and this file says so
    precisely rather than hiding it.** No theorem here exhibits a pair
    `(u, v)` with `convectiveTerm u v ≠ 0`. The reason is a missing
    primitive, not a missing idea: the pinned mathlib
    (`eed770a4`) has no concrete nonzero element of `𝓢(E, F)` — no
    Gaussian, bump-function, or compact-support Schwartz constructor —
    so no nonzero Schwartz field is available to feed in. What this
    file does instead is make the degeneracy question *exact*:

      `convective_eq_trivial_iff` — the convective carrier coincides
      with the constant-zero carrier `trivialBilinear` **iff** the
      convective derivative vanishes on every Schwartz pair;

      `full_eq_linearised_iff` — the full momentum residual coincides
      with the linearised (Stokes) residual **iff** the diagonal
      convective derivative vanishes on every Schwartz field.

    So both ch22 defects reduce to the single statement
    `∃ w, convectiveComponent w w i x ≠ 0`, whose only missing
    ingredient is one concrete nonzero Schwartz witness. That is the
    next brick, and it is a bounded task.

  • `bound_zero_constant_iff` shows the `C = 0` escape used by
    `trivialBilinear_satisfies_bound` is available **only** to operators
    whose output has identically vanishing `Ḣ^{1/2}` seminorm — so that
    discharge certifies nothing about a genuine nonlinearity.
    `bilinearBoundProp_convective_iff` unfolds `BilinearBoundProp`
    carried by the convective operator into the literal quadratic
    `Ḣ^{1/2}` estimate on `(u·∇)v`. That estimate is the substantive
    Fujita-Kato 1964 analytic content; it is **not** proved here.

  • **No progress is claimed on the Clay bar.**
    `VortexStretchingBoundedHypothesis` /
    `NS3DVortexStretchingObstruction` are untouched and remain OPEN.
    Nothing here is a regularity, global-existence, or no-blowup result.
    `IsNSSolution` is a predicate; the only solution exhibited is the
    zero solution (`zero_isNSSolution`), recorded so that the predicate
    is demonstrably non-vacuous.

  • The force slot of `IsNSSolution` imposes no time regularity on `f`,
    whereas Clay alternatives (C)/(D) additionally require
    `‖∂_x^m ∂_t^k f‖ ≤ C_{mk}(1+|x|+t)^{-K}`. The unconstrained-force
    theorem below is therefore a statement about this predicate's force
    slot, not about the Clay forced problem.

  • The mild formulation `B(u,v)(t) = ∫₀ᵗ e^{(t−s)Δ} P[(u·∇)v(s)] ds`
    still has no Bochner integral. `convectiveTransportShell` carries
    the *instantaneous* transport term `(u·∇)v`, not that integral; it
    inhabits `BilinearMildOperator` because that structure's two fields
    (the zero-input identities) do not pin the mild integral down. That
    underdetermination is itself a finding about the scaffold.

Fields are complexified (`C3 = EuclideanSpace ℂ (Fin 3)`), matching the
`FujitaKato1964` brick family.

No `sorry`, no `native_decide`, no project axioms.
Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-10-08)
-/

import PF.NavierStokes.FujitaKato1964.ConvectiveDerivative
import PF.NavierStokes.FujitaKato1964.BilinearScaffold

set_option autoImplicit false

namespace PF.NavierStokes.ConvectiveDerivativeConnection

open SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 ScalarSchwartz3C VectorSchwartz3C
   vectorHomogeneousH12SeminormSq
   vectorHomogeneousH12SeminormSq_nonneg)
open PF.NavierStokes.FujitaKato1964.VectorPartialDeriv
  (spatialDir partialDeriv partialDeriv_apply partialDeriv_zero partialDeriv_add)
open PF.NavierStokes.FujitaKato1964.ConvectiveDerivative
  (vectorComponent vectorComponent_apply
   convectiveComponent convectiveComponent_apply convectiveComponent_zero_left)
open PF.NavierStokes.FujitaKato1964.BilinearScaffold
  (TimeFieldR3C BilinearMildOperator BilinearBoundProp trivialBilinear)

/-! ## §1 — Temperate growth of vector Schwartz fields

`SchwartzMultiplication.lean` proves `Function.HasTemperateGrowth` for
*scalar* Schwartz functions. The reassembly of `(u·∇)v` into a vector
field multiplies the scalar component `u_j` against the **vector** field
`∂_j v`, so the temperate-growth witness is needed on the vector side.
The proof is the same two-field argument: smoothness from `smooth'`,
and the uniform bound from the `decay 0 n` slice of the Schwartz
condition. -/

/-- **Every vector Schwartz field on `R3` has temperate growth.**

For `u : 𝓢(R3, C3)` the certificate
`Function.HasTemperateGrowth (fun x => u x)` is the pair

  • `ContDiff ℝ ∞ u` — the `smooth'` field of `SchwartzMap`;
  • `∀ n, ∃ k C, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ C · (1 + ‖x‖)^k` —
    obtained from `u.decay 0 n`, which gives
    `‖x‖^0 · ‖iteratedFDeriv ℝ n u x‖ ≤ C`, i.e. the uniform bound
    `C · (1 + ‖x‖)^0` at `k = 0`.

This is the vector-valued analogue of
`SchwartzMultiplication.schwartzMap_hasTemperateGrowth`. -/
theorem vectorSchwartz_hasTemperateGrowth (u : VectorSchwartz3C) :
    Function.HasTemperateGrowth (fun x : R3 => u x) := by
  refine ⟨u.smooth', ?_⟩
  intro n
  obtain ⟨C, _hCpos, hC⟩ := u.decay 0 n
  refine ⟨0, C, ?_⟩
  intro x
  have hx := hC x
  simp only [pow_zero, one_mul] at hx
  simpa using hx

/-! ## §2 — The convective derivative as a vector Schwartz field

`ConvectiveDerivative.lean` delivers the three scalar components of
`(u·∇)v` separately. The momentum equation and the
`BilinearMildOperator` carrier both need them reassembled into one
`VectorSchwartz3C`. The `j`-th summand of `(u·∇)v` is the pointwise
scalar-times-vector product

  `x ↦ u_j(x) • (∂_j v)(x)`,

realised as `bilinLeftCLM (lsmul ℂ ℂ) h` evaluated at the scalar
Schwartz function `u_j = vectorComponent j u`, where `h` is the
temperate-growth witness of the vector field `∂_j v`. -/

/-- **`convectiveSummand u v j`** — the `j`-th summand
`u_j · (∂_j v)` of `(u·∇)v`, as a vector Schwartz field.

Built as `bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ) hg` applied to
the scalar Schwartz component `vectorComponent j u`, with
`g := (∂_j v : R3 → C3)` supplied by
`vectorSchwartz_hasTemperateGrowth`. The bilinear primitive
`lsmul ℂ ℂ : ℂ →L[ℂ] C3 →L[ℂ] C3` is complex scalar multiplication on
`C3`. -/
noncomputable def convectiveSummand (u v : VectorSchwartz3C) (j : Fin 3) :
    VectorSchwartz3C :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ)
    (vectorSchwartz_hasTemperateGrowth (partialDeriv j v)) (vectorComponent j u)

/-- **Pointwise content of `convectiveSummand`.**
At every `x : R3`,
`convectiveSummand u v j x = u x j • (∂_j v) x` — the literal
scalar-times-vector product, with the scalar supplied by
`vectorComponent_apply`. -/
theorem convectiveSummand_apply (u v : VectorSchwartz3C) (j : Fin 3) (x : R3) :
    convectiveSummand u v j x = (u x j) • (partialDeriv j v) x := by
  show (ContinuousLinearMap.lsmul ℂ ℂ) (vectorComponent j u x) ((partialDeriv j v) x) = _
  rw [vectorComponent_apply]
  rfl

/-- **★★★ `convectiveTerm u v`** — the convective derivative
`(u·∇)v` as a single vector Schwartz field:

  `convectiveTerm u v := Σ_{j : Fin 3} u_j · (∂_j v)`.

This is the object the momentum equation and the Fujita-Kato bilinear
carrier consume. Its components are exactly the scalar components
already built by `ConvectiveDerivative.convectiveComponent` — see
`convectiveTerm_component`. -/
noncomputable def convectiveTerm (u v : VectorSchwartz3C) : VectorSchwartz3C :=
  ∑ j : Fin 3, convectiveSummand u v j

/-- **Pointwise content of `convectiveTerm`.**
At every `x : R3`,
`convectiveTerm u v x = Σ_{j : Fin 3} u x j • (∂_j v) x`. -/
theorem convectiveTerm_apply (u v : VectorSchwartz3C) (x : R3) :
    convectiveTerm u v x = ∑ j : Fin 3, (u x j) • (partialDeriv j v) x := by
  unfold convectiveTerm
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [SchwartzMap.add_apply, convectiveSummand_apply]

/-- **★★★ THE CONNECTION ★★★**

The `i`-th component of the vector-valued convective derivative equals
the orphaned brick's scalar component:

  `convectiveTerm u v x i = convectiveComponent u v i x`.

This is the theorem the parity map asked for. From here on, every
statement in this file that mentions the nonlinear term is literally a
statement about
`PF.NavierStokes.FujitaKato1964.ConvectiveDerivative.convectiveComponent`,
so that brick is no longer formally inert. -/
theorem convectiveTerm_component (u v : VectorSchwartz3C) (x : R3) (i : Fin 3) :
    convectiveTerm u v x i = convectiveComponent u v i x := by
  rw [convectiveTerm_apply, convectiveComponent_apply,
      Fin.sum_univ_three, Fin.sum_univ_three]
  rfl

/-- **Vanishing criterion for the reassembled convective term.**

`convectiveTerm u v = 0` **iff** every scalar component of the orphaned
brick vanishes at every point. This is the form in which the
degeneracy question is used below: all degeneracy statements about the
vector-level object are statements about `convectiveComponent`. -/
theorem convectiveTerm_eq_zero_iff (u v : VectorSchwartz3C) :
    convectiveTerm u v = 0 ↔ ∀ (x : R3) (i : Fin 3), convectiveComponent u v i x = 0 := by
  constructor
  · intro h x i
    rw [← convectiveTerm_component, h]
    simp
  · intro h
    apply SchwartzMap.ext
    intro x
    ext i
    rw [convectiveTerm_component, h]
    simp

/-! ## §3 — Bilinearity of the reassembled convective term

`ConvectiveDerivative.lean` proved additivity in the first slot only.
At the vector level both slots are recorded, together with
complex homogeneity in the transporting slot. The transported slot is
only ℝ-homogeneous, because `partialDeriv` is the ℝ-linear
`pderivCLM ℝ`; that asymmetry is inherited, not introduced here. -/

/-- **`convectiveTerm 0 v = 0`** — vanishing transporting velocity. -/
theorem convectiveTerm_zero_left (v : VectorSchwartz3C) :
    convectiveTerm (0 : VectorSchwartz3C) v = 0 := by
  apply SchwartzMap.ext
  intro x
  rw [convectiveTerm_apply]
  simp

/-- **`convectiveTerm u 0 = 0`** — vanishing transported field, via
`partialDeriv_zero`. -/
theorem convectiveTerm_zero_right (u : VectorSchwartz3C) :
    convectiveTerm u (0 : VectorSchwartz3C) = 0 := by
  apply SchwartzMap.ext
  intro x
  rw [convectiveTerm_apply]
  simp [partialDeriv_zero]

/-- **Additivity in the transporting slot.** -/
theorem convectiveTerm_add_left (u u2 v : VectorSchwartz3C) :
    convectiveTerm (u + u2) v = convectiveTerm u v + convectiveTerm u2 v := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.add_apply, convectiveTerm_apply, convectiveTerm_apply,
      convectiveTerm_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  show ((u x) + (u2 x)) j • (partialDeriv j v) x
      = (u x j) • (partialDeriv j v) x + (u2 x j) • (partialDeriv j v) x
  rw [show ((u x) + (u2 x)) j = u x j + u2 x j from rfl, add_smul]

/-- **Additivity in the transported slot**, via `partialDeriv_add`. -/
theorem convectiveTerm_add_right (u v v2 : VectorSchwartz3C) :
    convectiveTerm u (v + v2) = convectiveTerm u v + convectiveTerm u v2 := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.add_apply, convectiveTerm_apply, convectiveTerm_apply,
      convectiveTerm_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [partialDeriv_add, SchwartzMap.add_apply, smul_add]

/-- **Complex homogeneity in the transporting slot.** -/
theorem convectiveTerm_smul_left (c : ℂ) (u v : VectorSchwartz3C) :
    convectiveTerm (c • u) v = c • convectiveTerm u v := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.smul_apply, convectiveTerm_apply, convectiveTerm_apply,
      Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  show (c • u x) j • (partialDeriv j v) x = c • ((u x j) • (partialDeriv j v) x)
  rw [show (c • u x) j = c * u x j from rfl, smul_smul]

/-! ## §4 — The convective term in the `BilinearMildOperator` slot

`BilinearScaffold.lean` declares the carrier
`BilinearMildOperator` — a bilinear on time fields plus the two
zero-input identities — and inhabits it with `trivialBilinear`, the
constant zero. The convective term now inhabits the same carrier with
its zero-input identities *proved* from the Schwartz-level lemmas.

Naming discipline: this is the **instantaneous** transport term
`(u·∇)v`, NOT the Fujita-Kato mild integral
`∫₀ᵗ e^{(t−s)Δ} P[(u·∇)v(s)] ds`. That both inhabit
`BilinearMildOperator` is a fact about the carrier: its two fields do
not determine the mild integral. -/

/-- **`convectiveTimeField u v`** — the convective derivative applied
slotwise in time: `t ↦ (u(t)·∇) v(t)`. -/
noncomputable def convectiveTimeField (u v : TimeFieldR3C) : TimeFieldR3C :=
  fun t => convectiveTerm (u t) (v t)

/-- **★ `convectiveTransportShell`** — the instantaneous convective
transport term as an inhabitant of `BilinearMildOperator`.

Unlike `trivialBilinear`, whose zero-input identities hold by `rfl`
because the operator is the constant zero, both identities here are
discharged from `convectiveTerm_zero_left` / `convectiveTerm_zero_right`,
i.e. from the actual vanishing behaviour of `(u·∇)v`. -/
noncomputable def convectiveTransportShell : BilinearMildOperator where
  B := convectiveTimeField
  zero_left v := by
    funext t
    exact convectiveTerm_zero_left (v t)
  zero_right u := by
    funext t
    exact convectiveTerm_zero_right (u t)

/-- **The carrier now literally carries the orphaned brick.**
`convectiveTransportShell.B u v t x i = convectiveComponent (u t) (v t) i x`. -/
theorem convectiveTransportShell_component
    (u v : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3) :
    convectiveTransportShell.B u v t x i = convectiveComponent (u t) (v t) i x :=
  convectiveTerm_component (u t) (v t) x i

/-- **The scaffold's only previous witness, in the same coordinates.**
`trivialBilinear.B u v t x i = 0` at every time, point and index. This
is the precise content of the ch22 ledger entry "THE BILINEAR MAP IS
THE CONSTANT ZERO". -/
theorem trivialBilinear_component
    (u v : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3) :
    trivialBilinear.B u v t x i = 0 := by
  show (0 : VectorSchwartz3C) x i = 0
  simp

/-! ## §5 — The degeneracy dichotomy, stated exactly

The ch22 defect is now a sharp equivalence rather than a verdict: the
genuine convective carrier collapses onto the constant-zero carrier
exactly on the locus where the convective derivative vanishes
identically. No nonzero Schwartz witness exists in the pinned mathlib,
so the collapse is not refuted here — but it is reduced to that single
missing witness. -/

/-- **★★ Degeneracy dichotomy for the bilinear carrier.**

The convective carrier agrees with the constant-zero carrier
`trivialBilinear` on *all* time-field pairs **iff** the convective
derivative `convectiveComponent` vanishes on *all* Schwartz pairs at
every point and index.

Forward: specialise to constant-in-time fields and evaluate at `t = 0`.
Backward: componentwise, through `convectiveTerm_component`.

Consequence: "the bilinear map is the constant zero" is no longer a
property of the *definition* once the convective carrier is used — it
becomes equivalent to a concrete analytic falsehood,
`∀ w z i x, Σ_j w_j(x) (∂_j z)_i(x) = 0`, which one nonzero Schwartz
witness refutes. -/
theorem convective_eq_trivial_iff :
    (∀ u v : TimeFieldR3C, convectiveTransportShell.B u v = trivialBilinear.B u v) ↔
      (∀ (w z : VectorSchwartz3C) (x : R3) (i : Fin 3),
        convectiveComponent w z i x = 0) := by
  constructor
  · intro h w z x i
    have h0 := congrFun (h (fun _ => w) (fun _ => z)) 0
    have h1 : convectiveTerm w z = 0 := h0
    rw [← convectiveTerm_component, h1]
    simp
  · intro h u v
    funext t
    apply SchwartzMap.ext
    intro x
    ext i
    rw [show convectiveTransportShell.B u v t = convectiveTerm (u t) (v t) from rfl,
        convectiveTerm_component, h, trivialBilinear_component]

/-- **★★ The `C = 0` discharge certifies nothing about a nonlinearity.**

`BilinearScaffold.trivialBilinear_satisfies_bound` discharges
`BilinearBoundProp` with the constant `C = 0`. This theorem shows what
that discharge is worth: for an arbitrary `B : BilinearMildOperator`,
the `C = 0` instance of the bilinear estimate holds **iff** the output
of `B` has identically vanishing `Ḣ^{1/2}` seminorm.

So the existing discharge is available only to operators that are
analytically invisible; it transfers to no operator with a nonvanishing
`Ḣ^{1/2}` output, in particular to no genuine Fujita-Kato bilinear. -/
theorem bound_zero_constant_iff (B : BilinearMildOperator) :
    (∀ (u v : TimeFieldR3C) (t : ℝ),
        vectorHomogeneousH12SeminormSq (B.B u v t)
          ≤ (0 : ℝ) ^ 2 * vectorHomogeneousH12SeminormSq (u t)
                        * vectorHomogeneousH12SeminormSq (v t)) ↔
      (∀ (u v : TimeFieldR3C) (t : ℝ),
        vectorHomogeneousH12SeminormSq (B.B u v t) = 0) := by
  constructor
  · intro h u v t
    have h1 := h u v t
    have h2 : (0 : ℝ) ^ 2 * vectorHomogeneousH12SeminormSq (u t)
                          * vectorHomogeneousH12SeminormSq (v t) = 0 := by ring
    rw [h2] at h1
    exact le_antisymm h1 (vectorHomogeneousH12SeminormSq_nonneg _)
  · intro h u v t
    have h2 : (0 : ℝ) ^ 2 * vectorHomogeneousH12SeminormSq (u t)
                          * vectorHomogeneousH12SeminormSq (v t) = 0 := by ring
    rw [h2, h u v t]

/-- **★★ `BilinearBoundProp`, carried by the convective term, is the
real Fujita-Kato estimate.**

Carried by `convectiveTransportShell`, the typed Prop
`BilinearBoundProp` is equivalent to the time-free quadratic estimate

  `‖(u·∇)v‖²_{Ḣ^{1/2}} ≤ C² · ‖u‖²_{Ḣ^{1/2}} · ‖v‖²_{Ḣ^{1/2}}`

on vector Schwartz fields. The time binder collapses because the
instantaneous transport term is pointwise in `t`; the forward direction
specialises to constant-in-time fields, the backward direction
instantiates at `(u t, v t)`.

This identifies exactly what remains open on the Fujita-Kato axis: the
estimate on the right-hand side is the published 1964 analytic content,
and it is **not** proved here. -/
theorem bilinearBoundProp_convective_iff :
    BilinearBoundProp convectiveTransportShell ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : VectorSchwartz3C,
        vectorHomogeneousH12SeminormSq (convectiveTerm u v)
          ≤ C ^ 2 * vectorHomogeneousH12SeminormSq u
                  * vectorHomogeneousH12SeminormSq v := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    intro u v
    exact h (fun _ => u) (fun _ => v) 0
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    intro u v t
    exact h (u t) (v t)

/-! ## §6 — The viscous term

`Δu = Σ_j ∂_j ∂_j u`, assembled from the same `partialDeriv` operator
the convective term uses, so the viscous and nonlinear slots of the
momentum equation are built from one differentiation primitive. -/

/-- **`vectorLaplacian u`** — the vector Laplacian
`Δu := Σ_{j : Fin 3} ∂_j (∂_j u)` on vector Schwartz fields. -/
noncomputable def vectorLaplacian (u : VectorSchwartz3C) : VectorSchwartz3C :=
  ∑ j : Fin 3, partialDeriv j (partialDeriv j u)

/-- **Pointwise content of `vectorLaplacian`**, componentwise. -/
theorem vectorLaplacian_apply (u : VectorSchwartz3C) (x : R3) (i : Fin 3) :
    vectorLaplacian u x i = ∑ j : Fin 3, (partialDeriv j (partialDeriv j u)) x i := by
  unfold vectorLaplacian
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rfl

/-- **`Δ0 = 0`**, from `partialDeriv_zero` applied twice. -/
theorem vectorLaplacian_zero :
    vectorLaplacian (0 : VectorSchwartz3C) = 0 := by
  unfold vectorLaplacian
  apply Finset.sum_eq_zero
  intro j _
  rw [partialDeriv_zero, partialDeriv_zero]

/-! ## §7 — The pressure term as a genuine gradient

The pressure slot must not be a free field: an unconstrained vector
field in the `∇p` position absorbs every residual and would make the
momentum equation vacuous. `IsPressureGradient` therefore requires the
slot to be the spatial gradient of a scalar pressure field — which is
exactly the constraint the Leray projection exists to enforce. -/

/-- **`scalarPartialDeriv i p`** — the `i`-th spatial partial derivative
of a scalar Schwartz function, via `SchwartzMap.pderivCLM ℝ` along
`spatialDir i`. The scalar companion of
`VectorPartialDeriv.partialDeriv`. -/
noncomputable def scalarPartialDeriv (i : Fin 3) (p : ScalarSchwartz3C) :
    ScalarSchwartz3C :=
  SchwartzMap.pderivCLM ℝ (spatialDir i) p

/-- **`∂_i 0 = 0`** on scalar Schwartz functions. -/
theorem scalarPartialDeriv_zero (i : Fin 3) :
    scalarPartialDeriv i (0 : ScalarSchwartz3C) = 0 := by
  unfold scalarPartialDeriv
  exact ContinuousLinearMap.map_zero _

/-- **`IsPressureGradient gradp`** — the time-dependent field `gradp`
is the spatial gradient of a time-dependent scalar pressure:

  `∃ p, ∀ t x i, gradp t x i = (∂_i p(t))(x)`.

Not every vector field satisfies this (gradients are curl-free), so
this is a genuine constraint on the pressure slot and blocks the
trivialisation in which `∇p` absorbs the whole equation. -/
def IsPressureGradient (gradp : TimeFieldR3C) : Prop :=
  ∃ p : ℝ → ScalarSchwartz3C,
    ∀ (t : ℝ) (x : R3) (i : Fin 3),
      gradp t x i = (scalarPartialDeriv i (p t)) x

/-- **The zero field is a pressure gradient** (`p = 0`). Recorded so
that the constraint is demonstrably satisfiable. -/
theorem isPressureGradient_zero :
    IsPressureGradient (fun _ => (0 : VectorSchwartz3C)) := by
  refine ⟨fun _ => (0 : ScalarSchwartz3C), ?_⟩
  intro t x i
  rw [scalarPartialDeriv_zero]
  simp

/-! ## §8 — The momentum equation

The incompressible Navier-Stokes momentum equation on `ℝ³`,

  `∂_t u + (u·∇)u = ν Δu − ∇p + f`,

written as the vanishing of the residual

  `R := ∂_t u + (u·∇)u − ν Δu + ∇p − f`.

Every slot is a real object: the convective slot is the orphaned
brick's `convectiveComponent`, the viscous slot is `vectorLaplacian`,
the pressure slot is constrained by `IsPressureGradient`, the time
derivative is a `HasDerivAt` on `t ↦ u(t)(x)_i`. -/

/-- **`momentumResidualField`** — the momentum residual as a vector
Schwartz field at each time:

  `R(t) := ∂_t u(t) + (u(t)·∇)u(t) − ν Δu(t) + ∇p(t) − f(t)`.

Being built from Schwartz-level operations, the residual is itself a
vector Schwartz field; this is what makes the force-absorption theorem
of §10 type-check. -/
noncomputable def momentumResidualField
    (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) : VectorSchwartz3C :=
  dtu t + convectiveTerm (u t) (u t) - (ν : ℂ) • vectorLaplacian (u t)
    + gradp t - f t

/-- **★★★ `momentumResidual`** — the pointwise momentum residual

  `R(t,x)_i = ∂_t u(t,x)_i + ((u·∇)u)(t,x)_i − ν (Δu)(t,x)_i
              + (∇p)(t,x)_i − f(t,x)_i`,

with the nonlinear slot filled by
`ConvectiveDerivative.convectiveComponent`. This is the first place in
the project where the Navier-Stokes momentum equation is written with
a non-inert nonlinear term. -/
noncomputable def momentumResidual
    (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3) : ℂ :=
  dtu t x i + convectiveComponent (u t) (u t) i x
    - (ν : ℂ) * vectorLaplacian (u t) x i + gradp t x i - f t x i

/-- **The field-level and pointwise residuals agree**, componentwise.
The bridge is `convectiveTerm_component`; everything else is the
definitional componentwise behaviour of `SchwartzMap` addition,
subtraction and scalar action. -/
theorem momentumResidualField_component
    (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3) :
    momentumResidualField ν u dtu gradp f t x i
      = momentumResidual ν u dtu gradp f t x i := by
  show dtu t x i + convectiveTerm (u t) (u t) x i
        - (ν : ℂ) * vectorLaplacian (u t) x i + gradp t x i - f t x i
      = momentumResidual ν u dtu gradp f t x i
  rw [convectiveTerm_component]
  rfl

/-- **`stokesResidual`** — the residual of the *linearised* (Stokes)
equation `∂_t u = ν Δu − ∇p + f`, i.e. `momentumResidual` with the
convective slot deleted. -/
noncomputable def stokesResidual
    (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3) : ℂ :=
  dtu t x i - (ν : ℂ) * vectorLaplacian (u t) x i + gradp t x i - f t x i

/-- **Full = linearised + nonlinear.**
`momentumResidual = stokesResidual + convectiveComponent (u t) (u t) i x`.
The exact separation of the two equations by the convective term. -/
theorem momentumResidual_eq_stokes_add_convective
    (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3) :
    momentumResidual ν u dtu gradp f t x i
      = stokesResidual ν u dtu gradp f t x i
        + convectiveComponent (u t) (u t) i x := by
  unfold momentumResidual stokesResidual
  ring

/-- **★★ "LINEARISED EQUALS FULL", stated exactly.**

The full momentum residual coincides with the linearised Stokes
residual, at every viscosity, field, time, point and index, **iff** the
diagonal convective derivative `convectiveComponent w w i x` vanishes
for every Schwartz field `w`.

This is the second ch22 ledger defect reduced to the same single
missing ingredient as the first: one nonzero Schwartz witness with a
nonvanishing diagonal transport term separates the full equation from
its linearisation. Until that witness exists the two residuals cannot
be separated in Lean — and that is now a precisely located gap rather
than a conflation. -/
theorem full_eq_linearised_iff :
    (∀ (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3),
        momentumResidual ν u dtu gradp f t x i
          = stokesResidual ν u dtu gradp f t x i) ↔
      (∀ (w : VectorSchwartz3C) (x : R3) (i : Fin 3),
        convectiveComponent w w i x = 0) := by
  constructor
  · intro h w x i
    have h0 := h 0 (fun _ => w) (fun _ => (0 : VectorSchwartz3C))
      (fun _ => (0 : VectorSchwartz3C)) (fun _ => (0 : VectorSchwartz3C)) 0 x i
    rw [momentumResidual_eq_stokes_add_convective] at h0
    exact add_eq_left.mp h0
  · intro h ν u dtu gradp f t x i
    rw [momentumResidual_eq_stokes_add_convective, h, add_zero]

/-! ## §9 — The Navier-Stokes solution predicate

`IsNSSolution ν u dtu gradp f T` is the Cauchy-problem predicate the
parity map asked for: a genuine PDE on a genuine time interval. The
horizon `T` appears in all three time-quantified clauses, so local and
global existence are **not** the same Prop — the defect recorded as
"`_T` is discarded" does not reproduce here. -/

/-- **★★★ `IsNSSolution ν u dtu gradp f T`** — `u` solves the
incompressible Navier-Stokes Cauchy problem with viscosity `ν`, pressure
gradient `gradp`, force `f`, on the time interval `[0, T]`:

  (1) `dtu` is the genuine time derivative: for every `t ∈ [0,T]`, every
      point `x` and index `i`,
      `HasDerivAt (fun s => u s x i) (dtu t x i) t`;
  (2) incompressibility: `Σ_j (∂_j u(t))(x)_j = 0` on `[0,T]`;
  (3) the pressure slot really is a gradient (`IsPressureGradient`);
  (4) the momentum equation: `momentumResidual = 0` on `[0,T]`.

All four clauses are constraints; see `zero_isNSSolution` for
non-vacuity. Nothing here asserts existence, uniqueness, or
regularity. -/
def IsNSSolution (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (T : ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : R3) (i : Fin 3),
      HasDerivAt (fun s : ℝ => u s x i) (dtu t x i) t) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : R3,
      ∑ j : Fin 3, (partialDeriv j (u t)) x j = 0) ∧
  IsPressureGradient gradp ∧
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : R3) (i : Fin 3),
      momentumResidual ν u dtu gradp f t x i = 0)

/-- **The predicate is non-vacuous: the zero field solves it.**

`u = 0`, `∂_t u = 0`, `∇p = 0`, `f = 0` satisfies all four clauses at
every viscosity and horizon — the time derivative by `hasDerivAt_const`,
incompressibility and the viscous slot by `partialDeriv_zero`, the
nonlinear slot by `convectiveComponent_zero_left`. Recorded so that no
later statement quantified over `IsNSSolution` can be vacuously true for
want of any solution at all. -/
theorem zero_isNSSolution (ν T : ℝ) :
    IsNSSolution ν (fun _ => (0 : VectorSchwartz3C))
      (fun _ => (0 : VectorSchwartz3C)) (fun _ => (0 : VectorSchwartz3C))
      (fun _ => (0 : VectorSchwartz3C)) T := by
  refine ⟨?_, ?_, isPressureGradient_zero, ?_⟩
  · intro t _ x i
    exact hasDerivAt_const t (0 : ℂ)
  · intro t _ x
    apply Finset.sum_eq_zero
    intro j _
    rw [partialDeriv_zero]
    simp
  · intro t _ x i
    unfold momentumResidual
    rw [convectiveComponent_zero_left, vectorLaplacian_zero]
    simp

/-- **The force enters as an exact additive shift.**

`momentumResidual` with force `f` equals the unforced residual minus
`f t x i`. Nothing about the equation's structure is changed by
forcing; only the right-hand side moves. -/
theorem momentumResidual_force_shift
    (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3) :
    momentumResidual ν u dtu gradp f t x i
      = momentumResidual ν u dtu gradp (fun _ => (0 : VectorSchwartz3C)) t x i
        - f t x i := by
  unfold momentumResidual
  show _ = (dtu t x i + convectiveComponent (u t) (u t) i x
      - (ν : ℂ) * vectorLaplacian (u t) x i + gradp t x i
      - (0 : C3) i) - f t x i
  simp

/-- **Solving the forced equation = prescribing the unforced residual.**

`u` kills the forced residual on `[0,T]` **iff** its unforced residual
equals the force there. The forced problem is therefore the unforced
operator with a prescribed right-hand side — the exact sense in which
the two problems differ. -/
theorem nsSolution_forced_iff_unforced_residual_eq_force
    (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (T : ℝ) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : R3) (i : Fin 3),
        momentumResidual ν u dtu gradp f t x i = 0) ↔
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : R3) (i : Fin 3),
        momentumResidual ν u dtu gradp (fun _ => (0 : VectorSchwartz3C)) t x i
          = f t x i) := by
  constructor
  · intro h t ht x i
    have h1 := h t ht x i
    rw [momentumResidual_force_shift] at h1
    exact sub_eq_zero.mp h1
  · intro h t ht x i
    rw [momentumResidual_force_shift, h t ht x i, sub_self]

/-! ## §10 — Forced versus unforced, kept explicit

The 2026 external results establish finite-time blow-up for 3-D
incompressible Navier-Stokes **with forcing** and for **unforced
Euler** on `ℝ³`, settling Clay alternatives (C) and (D). Alternatives
(A) and (B) — unforced Navier-Stokes — remain open. This section
records formally why a forced blow-up result does not touch the
unforced reading. -/

/-- **Forced scope is at least as strong as unforced scope.**

If a conclusion `P u` is established for every solution with *every*
force, it follows for the unforced solutions (instantiate `f = 0`).

Contrapositively: refuting `P` on the forced class — which is what the
2026 blow-up results do for global regularity — does not refute it on
the unforced class. The converse implication is **not** provable and is
not claimed. -/
theorem forced_scope_implies_unforced_scope
    (P : TimeFieldR3C → Prop) (ν T : ℝ)
    (h : ∀ u dtu gradp f : TimeFieldR3C, IsNSSolution ν u dtu gradp f T → P u) :
    ∀ u dtu gradp : TimeFieldR3C,
      IsNSSolution ν u dtu gradp (fun _ => (0 : VectorSchwartz3C)) T → P u :=
  fun u dtu gradp hu => h u dtu gradp _ hu

/-- **★★ The force slot absorbs every residual.**

Every time-differentiable, divergence-free Schwartz velocity field with
a legitimate pressure gradient solves the *forced* Navier-Stokes system
for some force — namely the force equal to its own unforced residual,
which is itself a vector Schwartz field (`momentumResidualField`).

So at this predicate's level the forced problem imposes **no**
constraint on `u` beyond time-differentiability and incompressibility,
while the unforced problem (`f = 0`) is a genuine constraint. This is
the formal reason a forced blow-up construction cannot be read as
progress on, or against, the unforced question.

Scope caveat: the Clay alternatives (C)/(D) additionally demand
space-time decay of `f`
(`‖∂_x^m ∂_t^k f‖ ≤ C_{mk}(1+|x|+t)^{-K}`), which this predicate's
force slot does not require. The theorem is a statement about this
predicate, not about the Clay forced problem. -/
theorem exists_force_for_every_divfree_field
    (ν : ℝ) (u dtu gradp : TimeFieldR3C) (T : ℝ)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : R3) (i : Fin 3),
        HasDerivAt (fun s : ℝ => u s x i) (dtu t x i) t)
    (hdiv : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : R3,
        ∑ j : Fin 3, (partialDeriv j (u t)) x j = 0)
    (hp : IsPressureGradient gradp) :
    ∃ f : TimeFieldR3C, IsNSSolution ν u dtu gradp f T := by
  refine ⟨fun t => momentumResidualField ν u dtu gradp
      (fun _ => (0 : VectorSchwartz3C)) t, hd, hdiv, hp, ?_⟩
  intro t _ x i
  rw [momentumResidual_force_shift, momentumResidualField_component]
  simp

/-! ## §11 — Capstone -/

/-- **★★★ Convective-derivative connection capstone ★★★**

Bundles the repair:

  (a) **The connection.** The vector-valued convective derivative's
      components are exactly `ConvectiveDerivative.convectiveComponent`
      — the orphaned brick is now consumed.
  (b) **The bilinear carrier** of `BilinearScaffold` carries it, and the
      previous witness `trivialBilinear` is the constant zero in the same
      coordinates.
  (c) **Degeneracy dichotomy.** The two carriers coincide iff the
      convective derivative vanishes identically.
  (d) **The `C = 0` escape.** The bilinear estimate at `C = 0` holds iff
      the operator's `Ḣ^{1/2}` output vanishes identically — so the
      existing discharge certifies nothing about a nonlinearity.
  (e) **Full = linearised + nonlinear**, and the two coincide iff the
      diagonal convective derivative vanishes identically.
  (f) **The momentum equation is written**, with a non-vacuous solution
      predicate on a load-bearing time interval.
  (g) **Forced vs unforced.** Forcing is an exact additive shift; forced
      scope implies unforced scope; and the force slot absorbs every
      residual, so the forced class is unconstrained beyond
      incompressibility at this layer.

Open, and not touched: the quadratic `Ḣ^{1/2}` bilinear estimate (the
published Fujita-Kato 1964 analytic content); the existence of a
nonzero Schwartz witness separating the convective term from zero; and
the Clay bar itself — `VortexStretchingBoundedHypothesis` /
`NS3DVortexStretchingObstruction` remain OPEN.

Kernel-only: `[propext, Classical.choice, Quot.sound]`. -/
theorem convectiveDerivative_connection_capstone :
    -- (a) the connection
    (∀ (u v : VectorSchwartz3C) (x : R3) (i : Fin 3),
        convectiveTerm u v x i = convectiveComponent u v i x) ∧
    -- (b) the bilinear carrier, both witnesses in one coordinate system
    (∀ (u v : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3),
        convectiveTransportShell.B u v t x i = convectiveComponent (u t) (v t) i x) ∧
    (∀ (u v : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3),
        trivialBilinear.B u v t x i = 0) ∧
    -- (c) degeneracy dichotomy
    ((∀ u v : TimeFieldR3C, convectiveTransportShell.B u v = trivialBilinear.B u v) ↔
      (∀ (w z : VectorSchwartz3C) (x : R3) (i : Fin 3),
        convectiveComponent w z i x = 0)) ∧
    -- (d) the `C = 0` escape, and the real estimate it hides
    (∀ B : BilinearMildOperator,
      (∀ (u v : TimeFieldR3C) (t : ℝ),
          vectorHomogeneousH12SeminormSq (B.B u v t)
            ≤ (0 : ℝ) ^ 2 * vectorHomogeneousH12SeminormSq (u t)
                          * vectorHomogeneousH12SeminormSq (v t)) ↔
        (∀ (u v : TimeFieldR3C) (t : ℝ),
          vectorHomogeneousH12SeminormSq (B.B u v t) = 0)) ∧
    (BilinearBoundProp convectiveTransportShell ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : VectorSchwartz3C,
        vectorHomogeneousH12SeminormSq (convectiveTerm u v)
          ≤ C ^ 2 * vectorHomogeneousH12SeminormSq u
                  * vectorHomogeneousH12SeminormSq v) ∧
    -- (e) full versus linearised
    (∀ (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3),
        momentumResidual ν u dtu gradp f t x i
          = stokesResidual ν u dtu gradp f t x i
            + convectiveComponent (u t) (u t) i x) ∧
    ((∀ (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3),
        momentumResidual ν u dtu gradp f t x i
          = stokesResidual ν u dtu gradp f t x i) ↔
      (∀ (w : VectorSchwartz3C) (x : R3) (i : Fin 3),
        convectiveComponent w w i x = 0)) ∧
    -- (f) the solution predicate is non-vacuous
    (∀ ν T : ℝ, IsNSSolution ν (fun _ => (0 : VectorSchwartz3C))
        (fun _ => (0 : VectorSchwartz3C)) (fun _ => (0 : VectorSchwartz3C))
        (fun _ => (0 : VectorSchwartz3C)) T) ∧
    -- (g) forced versus unforced
    (∀ (ν : ℝ) (u dtu gradp f : TimeFieldR3C) (t : ℝ) (x : R3) (i : Fin 3),
        momentumResidual ν u dtu gradp f t x i
          = momentumResidual ν u dtu gradp (fun _ => (0 : VectorSchwartz3C)) t x i
            - f t x i) ∧
    (∀ (P : TimeFieldR3C → Prop) (ν T : ℝ),
      (∀ u dtu gradp f : TimeFieldR3C, IsNSSolution ν u dtu gradp f T → P u) →
        ∀ u dtu gradp : TimeFieldR3C,
          IsNSSolution ν u dtu gradp (fun _ => (0 : VectorSchwartz3C)) T → P u) :=
  ⟨convectiveTerm_component,
   convectiveTransportShell_component,
   trivialBilinear_component,
   convective_eq_trivial_iff,
   bound_zero_constant_iff,
   bilinearBoundProp_convective_iff,
   momentumResidual_eq_stokes_add_convective,
   full_eq_linearised_iff,
   zero_isNSSolution,
   momentumResidual_force_shift,
   forced_scope_implies_unforced_scope⟩

/-! ## §12 — Axiom audit -/

#print axioms vectorSchwartz_hasTemperateGrowth
#print axioms convectiveSummand
#print axioms convectiveSummand_apply
#print axioms convectiveTerm
#print axioms convectiveTerm_apply
#print axioms convectiveTerm_component
#print axioms convectiveTerm_eq_zero_iff
#print axioms convectiveTerm_zero_left
#print axioms convectiveTerm_zero_right
#print axioms convectiveTerm_add_left
#print axioms convectiveTerm_add_right
#print axioms convectiveTerm_smul_left
#print axioms convectiveTransportShell
#print axioms convectiveTransportShell_component
#print axioms trivialBilinear_component
#print axioms convective_eq_trivial_iff
#print axioms bound_zero_constant_iff
#print axioms bilinearBoundProp_convective_iff
#print axioms vectorLaplacian
#print axioms vectorLaplacian_apply
#print axioms vectorLaplacian_zero
#print axioms scalarPartialDeriv
#print axioms scalarPartialDeriv_zero
#print axioms isPressureGradient_zero
#print axioms momentumResidualField
#print axioms momentumResidual
#print axioms momentumResidualField_component
#print axioms stokesResidual
#print axioms momentumResidual_eq_stokes_add_convective
#print axioms full_eq_linearised_iff
#print axioms zero_isNSSolution
#print axioms momentumResidual_force_shift
#print axioms nsSolution_forced_iff_unforced_residual_eq_force
#print axioms forced_scope_implies_unforced_scope
#print axioms exists_force_for_every_divfree_field
#print axioms convectiveDerivative_connection_capstone

end PF.NavierStokes.ConvectiveDerivativeConnection

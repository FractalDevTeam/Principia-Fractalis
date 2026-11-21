/-
# Fefferman (C)/(D): breakdown with force — the target the 2026 chain aims at

**Date**: 2026-11-21 (Legion).

Fefferman's official Clay statement has **four** parts, and the prize is
for any one of them:

* **(A)** existence and smoothness for unforced NS on `ℝ³`;
* **(B)** the same on the torus;
* **(C)** **breakdown** on `ℝ³` *with* an admissible force;
* **(D)** breakdown on the torus with an admissible force.

`Fefferman2000_Faithful_Statement_2026_10_12.lean` states (A). This file
states **(C)**, because that is the statement a *forced* blow-up result
settles — and the 2026 Córdoba–Martínez-Zoroa / Buckmaster–Alpöge /
OpenAI-formalized chain is a forced-NS / unforced-Euler blow-up chain,
not an unforced-NS regularity result.

## Why this file exists

`codex/NS_SCOPING_CARRIER_IS_THE_BLOCKER_2026-10-17.md` §5 records the
corpus's own adjudication: that chain **does not settle (A)/(B)**, those
are "untouched", and the α-web nevertheless cites it as a "second settled
anchor" for `α_NS = 3π/2` alongside Perelman. The ledger's open item is
exactly:

> whether the 2026 chain's forcing meets that admissibility condition is
> exactly what decides whether it settles a Clay statement or sits beside
> one. **OPEN: verify the forcing bounds against the papers.**

So the right move is not to argue about it but to **write the target**.
With (C) stated faithfully, a forced blow-up result either instantiates it
or does not, and the question becomes a finite check against the papers
rather than a standing ambiguity.

## The sharp point, proved below

`forced_momentum_at_zero_forcing` : with `f ≡ 0` the forced momentum
equation **is** the unforced one, syntactically. So a blow-up with zero
forcing would bear on (A); a blow-up with nonzero forcing bears on (C).
**The forcing is doing all of the work**, which is precisely why its
admissibility is the whole question. `admissibleForcing_zero` shows the
admissible class is non-empty, so (C) is not vacuous for lack of
candidate forces.

## What this file does NOT do

It does not claim (C) is settled, does not claim the 2026 chain's forcing
is admissible, and does not verify any paper — the primary sources are
not in hand here. It states the target and isolates the one condition
that decides the matter.
-/

import PF.NavierStokes.Fefferman2000_Faithful_GeometricDepletion_2026_11_21

open MeasureTheory

namespace PF.NavierStokes.FeffermanFaithful

/-! ## §1 — Admissible forcing

Fefferman requires the force to satisfy, for all multi-orders `α`, all
time-orders `m` and all `K`,

    `|∂ᵅₓ ∂ᵐₜ f(x,t)| ≤ C_{αmK} (1 + |x| + t)^(-K)`

i.e. every space-time derivative decays faster than any polynomial in
`(1 + |x| + t)`. Below, the mixed multi-order `(α, m)` is carried by the
joint iterated derivative of order `n` on `V × ℝ`, which quantifies over
all mixed orders at once. -/

/-- **Fefferman's admissibility condition on the force.** Every joint
    space-time derivative of every order decays faster than every
    polynomial rate in `1 + |x| + t`, on the forward half-space. -/
def AdmissibleForcing (f : V × ℝ → V) : Prop :=
  ∀ n K : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ q : V × ℝ, 0 ≤ q.2 →
      ‖iteratedFDeriv ℝ n f q‖ ≤ C * (1 + ‖q.1‖ + q.2) ^ (-(K : ℝ))

/-- **The admissible class is non-empty**: the zero force is admissible.

    So (C) below is not vacuous for want of a candidate force, and the
    question of whether a *given* force is admissible is a real one. -/
theorem admissibleForcing_zero : AdmissibleForcing (fun _ : V × ℝ => (0 : V)) := by
  intro n K
  refine ⟨1, one_pos, fun q hq => ?_⟩
  have hz : ‖iteratedFDeriv ℝ n (fun _ : V × ℝ => (0 : V)) q‖ = 0 := by simp
  have hbase : (0 : ℝ) < 1 + ‖q.1‖ + q.2 := by
    have := norm_nonneg q.1
    linarith
  rw [hz, one_mul]
  exact le_of_lt (Real.rpow_pos_of_pos hbase _)

/-! ## §2 — The forced equations -/

/-- The forced momentum equation at a point:
    `∂ₜu + (u·∇)u + ∇p = νΔu + f`. -/
def ForcedMomentumAt (ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ)
    (f : V × ℝ → V) (x : V) (t : ℝ) : Prop :=
  deriv (fun s : ℝ => U (x, s)) t
    + fderiv ℝ (fun y : V => U (y, t)) x (U (x, t))
    + gradient (fun y : V => P (y, t)) x
  = ν • InnerProductSpace.laplacian (fun y : V => U (y, t)) x + f (x, t)

/-- **★ The forcing is doing all the work.**

    With `f ≡ 0` the forced momentum equation is *literally* the unforced
    one — the same proposition, not merely an analogue. Hence a blow-up
    construction with zero forcing would bear on Fefferman (A), and one
    with nonzero forcing bears on (C). That is why the admissibility of
    the particular force is the entire question, and why a forced result
    cannot be cited against (A). -/
theorem forced_momentum_at_zero_forcing (ν : ℝ) (U : V × ℝ → V)
    (P : V × ℝ → ℝ) (x : V) (t : ℝ) :
    ForcedMomentumAt ν U P (fun _ => (0 : V)) x t
      ↔ (deriv (fun s : ℝ => U (x, s)) t
          + fderiv ℝ (fun y : V => U (y, t)) x (U (x, t))
          + gradient (fun y : V => P (y, t)) x
        = ν • InnerProductSpace.laplacian (fun y : V => U (y, t)) x) := by
  unfold ForcedMomentumAt
  simp

/-- A global smooth forced solution with bounded energy, for datum `u₀`
    and force `f` — the object (C) asserts cannot exist. -/
def HasGlobalForcedSolution (u0 : SchwartzMap V V) (f : V × ℝ → V) : Prop :=
  ∃ (ν : ℝ) (U : V × ℝ → V) (P : V × ℝ → ℝ),
    0 < ν ∧
    ContDiffOn ℝ (⊤ : ℕ∞) U {q : V × ℝ | 0 ≤ q.2} ∧
    ContDiffOn ℝ (⊤ : ℕ∞) P {q : V × ℝ | 0 ≤ q.2} ∧
    (∀ x : V, U (x, 0) = u0 x) ∧
    (∀ (x : V) (t : ℝ), 0 ≤ t → divergence (fun y => U (y, t)) x = 0) ∧
    (∀ (x : V) (t : ℝ), 0 ≤ t → ForcedMomentumAt ν U P f x t) ∧
    HasBoundedEnergyOn U (Set.Ici 0)

/-! ## §3 — Fefferman (C) -/

/-- **Fefferman (C): breakdown of Navier-Stokes on `ℝ³` with force.**

    There exist an admissible initial datum and an admissible force for
    which no global smooth bounded-energy solution exists.

    Proving this **is** a Clay solution — (C) is one of Fefferman's four
    alternatives, not a weaker consolation. What it is *not* is (A): it
    says nothing about the unforced problem.

    This is the statement a forced blow-up result instantiates. Whether
    the 2026 chain does instantiate it reduces entirely to whether its
    force satisfies `AdmissibleForcing`. -/
def Clay_NS_BreakdownWithForce_Fefferman2000_C : Prop :=
  ∃ (u0 : SchwartzMap V V) (f : V × ℝ → V),
    AdmissibleDatum u0 ∧ AdmissibleForcing f ∧ ¬ HasGlobalForcedSolution u0 f

/-- **(C) and (A) are different targets.**

    A witness for (C) supplies a *force*; (A) quantifies over the
    unforced problem only. The bridge between them would require the
    witness force to be zero, and `forced_momentum_at_zero_forcing` is
    the only point at which the two equations coincide. Recorded as the
    reason a forced blow-up must not be cited against (A). -/
theorem breakdown_with_force_needs_the_force
    (u0 : SchwartzMap V V) (f : V × ℝ → V)
    (hf : ∀ q : V × ℝ, f q = 0)
    (h : ¬ HasGlobalForcedSolution u0 f) :
    ¬ HasGlobalForcedSolution u0 (fun _ => (0 : V)) := by
  intro hcon
  apply h
  obtain ⟨ν, U, P, hν, hU, hP, hinit, hdiv, hmom, hE⟩ := hcon
  refine ⟨ν, U, P, hν, hU, hP, hinit, hdiv, fun x t ht => ?_, hE⟩
  have := hmom x t ht
  unfold ForcedMomentumAt at this ⊢
  rw [hf (x, t)]
  exact this

#print axioms admissibleForcing_zero
#print axioms forced_momentum_at_zero_forcing
#print axioms breakdown_with_force_needs_the_force
#print Clay_NS_BreakdownWithForce_Fefferman2000_C

end PF.NavierStokes.FeffermanFaithful

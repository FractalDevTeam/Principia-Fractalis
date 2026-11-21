/-
# 2D Navier-Stokes: the enstrophy argument, stated with content

**Date**: 2026-11-20

`PF/NS2DGlobalRegularity.lean` proves the Galerkin enstrophy argument
genuinely — `vorticity_rhs_inner_with_omega`, `vorticity_L2_dissipation`
and `vorticity_L2_norm_nonincreasing` are real theorems with real proofs
from the structure's own hypotheses (divergence-free transport, PSD
diffusion, non-negative viscosity).

Three things in that file carried no content when this one was written:

* `vortex_stretching_2D_term (_ω _u) := 0` — both arguments unused, then
  proved zero by `rfl`. That is `0 = 0`.
* `BKM_criterion_satisfied_2D : Prop := True`
* `NavierStokes2DGlobalRegularity : Prop := True`

**Update (later on 2026-11-20).** The latter two were retired: both now
carry the real Galerkin enstrophy statements, proved from
`Vorticity2DSystem`'s own hypotheses, and `NS2DGlobalRegularity.lean` has
no `: Prop := True` left. The first remains as described.

This module supplies the statements those three were meant to carry,
proved from the existing theorems. Nothing here is asserted and nothing
is a placeholder.

**Scope, stated once.** This is the finite-dimensional enstrophy
argument. It is NOT the Clay-form 2D theorem (Ladyzhenskaya 1959), which
requires Sobolev spaces, the Leray projection and a PDE solution concept
mathlib does not carry. The 3D global statement is the open Millennium
problem and nothing here touches it.
-/

import PF.NS2DGlobalRegularity

namespace PrincipiaTractalis.NS2DGlobalRegularity

variable {n : ℕ}

/-! ## §1 — The enstrophy contribution of a candidate extra term -/

/-- What a candidate extra vorticity term `S` adds to
    `d/dt ‖ω‖²/2 = ⟨ω', ω⟩`. -/
noncomputable def enstrophyContribution
    (S : Vorticity2DState n → Vorticity2DState n → Vorticity2DState n)
    (ω u : Vorticity2DState n) : ℝ :=
  inner ℝ (S ω u) ω

/-- **★ The 2D enstrophy balance is exact.**

    With divergence-free transport and PSD diffusion the rate is
    exactly `-ν⟨Lω,ω⟩`; an added term shifts it by exactly that term's
    enstrophy contribution, with no residual slack. -/
theorem enstrophy_rate_exact (V : Vorticity2DSystem n)
    (S : Vorticity2DState n → Vorticity2DState n → Vorticity2DState n)
    (u ω : Vorticity2DState n) :
    inner ℝ (V.rhs u ω + S ω u) ω
      = - V.ν * inner ℝ (V.L ω) ω + enstrophyContribution S ω u := by
  unfold enstrophyContribution
  rw [inner_add_left, vorticity_rhs_inner_with_omega]

/-- **★ Dissipation survives an added term exactly when that term does
    not inject more enstrophy than the viscous sink removes.**

    This is the 2D/3D gap stated with content: in 2D the transport
    identity makes the sink the only slack, so the condition is
    checkable; in 3D the stretching term `(ω·∇)u` has no sign control
    on this quantity and the argument fails. -/
theorem dissipation_iff_contribution_le (V : Vorticity2DSystem n)
    (S : Vorticity2DState n → Vorticity2DState n → Vorticity2DState n)
    (u ω : Vorticity2DState n) :
    inner ℝ (V.rhs u ω + S ω u) ω ≤ 0
      ↔ enstrophyContribution S ω u ≤ V.ν * inner ℝ (V.L ω) ω := by
  rw [enstrophy_rate_exact V S u ω]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **★ An added term leaves the rate unchanged iff its contribution
    vanishes identically.**

    The precise sense in which 2D hosts no stretching term: not that a
    definition was set to zero, but that the balance tolerates no
    enstrophy-shifting bilinear term. -/
theorem contribution_zero_iff_rate_unchanged (V : Vorticity2DSystem n)
    (S : Vorticity2DState n → Vorticity2DState n → Vorticity2DState n) :
    (∀ u ω : Vorticity2DState n,
        inner ℝ (V.rhs u ω + S ω u) ω = inner ℝ (V.rhs u ω) ω)
      ↔ (∀ u ω : Vorticity2DState n, enstrophyContribution S ω u = 0) := by
  constructor
  · intro h u ω
    have hx := h u ω
    rw [enstrophy_rate_exact V S u ω, vorticity_rhs_inner_with_omega] at hx
    linarith
  · intro h u ω
    rw [enstrophy_rate_exact V S u ω, vorticity_rhs_inner_with_omega, h u ω]
    ring

/-! ## §2 — What this file delivers, named accurately -/

/-- **2D Galerkin enstrophy non-increase.** Quantified over every mode
    count, every system satisfying the hypotheses, and every state. -/
def NS2DGalerkinEnstrophyNonincreasing : Prop :=
  ∀ (m : ℕ) (V : Vorticity2DSystem m) (u ω : Vorticity2DState m),
    inner ℝ (V.rhs u ω) ω ≤ 0

/-- **★ It holds** — proved, not asserted. -/
theorem ns2d_galerkin_enstrophy_nonincreasing :
    NS2DGalerkinEnstrophyNonincreasing :=
  fun _m V u ω => vorticity_L2_dissipation V u ω

/-- **The enstrophy half of the BKM ingredient.**

    BKM needs `∫₀^T ‖ω(t)‖_∞ dt < ∞`. Proved here: the L² rate is
    non-positive in both argument orders, so L² vorticity cannot grow
    along the Galerkin flow. The step to the L^∞ integral needs the 2D
    Sobolev embedding and a solution concept and is NOT claimed. -/
def NS2DEnstrophyBoundSupportsBKM : Prop :=
  ∀ (m : ℕ) (V : Vorticity2DSystem m) (u ω : Vorticity2DState m),
    inner ℝ ω (V.rhs u ω) ≤ 0 ∧ inner ℝ (V.rhs u ω) ω ≤ 0

/-- **★ The enstrophy half holds** (axiom-free). -/
theorem ns2d_enstrophy_bound_supports_bkm :
    NS2DEnstrophyBoundSupportsBKM :=
  fun _m V u ω =>
    ⟨vorticity_L2_norm_nonincreasing V u ω, vorticity_L2_dissipation V u ω⟩

#print axioms ns2d_galerkin_enstrophy_nonincreasing
#print axioms ns2d_enstrophy_bound_supports_bkm
#print axioms enstrophy_rate_exact
#print axioms dissipation_iff_contribution_le
#print axioms contribution_zero_iff_rate_unchanged

end PrincipiaTractalis.NS2DGlobalRegularity

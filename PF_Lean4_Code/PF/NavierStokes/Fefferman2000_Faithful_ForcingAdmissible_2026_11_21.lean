/-
# Compactly supported forcing is Fefferman-admissible

**Date**: 2026-11-21 (Legion).

`Fefferman2000_Faithful_BreakdownWithForce_2026_11_21.lean` states
Fefferman (C) and names `AdmissibleForcing` — his decay condition on the
external force. The corpus ledger
(`codex/NS_SCOPING_CARRIER_IS_THE_BLOCKER_2026-10-17.md` §5) carried a
standing open item: **verify the 2026 chain's forcing against that
condition.**

## The primary sources, read 2026-11-21

OpenAI, *Finite Time Blowup for Navier–Stokes* (2026-09-08), with the
expository companions Lei–Ren Part I (arXiv:2609.35406, "We claim no
original mathematical contribution") and Part II (arXiv:2611.06869,
2026-11-04). Part II's Theorem 1.1 states the force as

    `f ∈ C_c^∞(ℝ³ × (0,∞), ℝ³)`

— smooth and **compactly supported in space-time** — with finite energy
`sup_{0≤t<1}‖u(t)‖_{L²} + ‖∇u‖_{L²(ℝ³×[0,1])} < ∞`, on `ℝ³`, full
viscosity, and `‖u(t)‖_{L^∞} ≥ c(1−t)^{−(1+δ)/2} → ∞` as `t ↑ 1`.

## What this file proves

Compact support is **strictly stronger** than Fefferman's requirement.
Off the support every derivative vanishes, so the bound is trivial; on
the support `(1 + ‖x‖ + t)` is bounded above, so the negative power is
bounded below and a single constant works for every order and every `K`.

`admissibleForcing_of_bounded_support` proves it. The hypotheses are
exactly the two facts "smooth with compact support" supplies: all
iterated derivatives vanish outside a bounded region, and each is
globally bounded.

**So the ledger's open item is closed, in the affirmative, for the
forcing condition.** A smooth compactly supported force meets
Fefferman's admissibility.

## What this does NOT settle

Fefferman (C) also requires the **initial datum** to be admissible —
smooth, divergence-free, with rapid decay (his condition (4)). The
extracted statements do not record `u(·,0)`'s decay, so that half is not
verified here and is the remaining check.

And there is live criticism of what the construction means: that it
exhibits blow-up driven by inviscid (Euler) dynamics assisted by an
external force rather than by Navier–Stokes dynamics (J. L. Nielsen,
*The OpenAI Navier–Stokes Result Is an Euler Blowup in Disguise*), and
there is a documented priority controversy. Those bear on
interpretation, not on whether the forcing is admissible.

**Nothing here claims Fefferman (C) is proved, and nothing here touches
(A).** (A) — unforced global regularity — is untouched by a forced
blow-up, which is exactly what `forced_momentum_at_zero_forcing` makes
precise.
-/

import PF.NavierStokes.Fefferman2000_Faithful_BreakdownWithForce_2026_11_21

namespace PF.NavierStokes.FeffermanFaithful

/-- **★ A smooth, compactly supported force is Fefferman-admissible.**

    Hypotheses are the two consequences of `f ∈ C_c^∞`: every iterated
    derivative vanishes outside a bounded region (`hvanish`), and each is
    globally bounded (`hbound`).

    This closes the corpus ledger's standing open item on the 2026
    forced-blow-up chain's forcing, whose force is stated as
    `f ∈ C_c^∞(ℝ³ × (0,∞), ℝ³)`. -/
theorem admissibleForcing_of_bounded_support
    (f : V × ℝ → V) (R : ℝ) (hR : 0 ≤ R)
    (hvanish : ∀ (n : ℕ) (q : V × ℝ), R < ‖q.1‖ + q.2 →
      iteratedFDeriv ℝ n f q = 0)
    (hbound : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ q : V × ℝ, ‖iteratedFDeriv ℝ n f q‖ ≤ B) :
    AdmissibleForcing f := by
  intro n K
  obtain ⟨B, hB0, hB⟩ := hbound n
  have hR1 : (0 : ℝ) < 1 + R := by linarith
  refine ⟨B * (1 + R) ^ (K : ℝ) + 1, ?_, fun q hq => ?_⟩
  · have : (0 : ℝ) < (1 + R) ^ (K : ℝ) := Real.rpow_pos_of_pos hR1 _
    positivity
  · have hx : (0 : ℝ) ≤ ‖q.1‖ := norm_nonneg _
    have hb : (0 : ℝ) < 1 + ‖q.1‖ + q.2 := by linarith
    by_cases h : R < ‖q.1‖ + q.2
    · -- off the support: the left side is zero
      rw [hvanish n q h, norm_zero]
      have hpos : (0 : ℝ) < (1 + ‖q.1‖ + q.2) ^ (-(K : ℝ)) :=
        Real.rpow_pos_of_pos hb _
      have hC : (0 : ℝ) < B * (1 + R) ^ (K : ℝ) + 1 := by
        have : (0 : ℝ) < (1 + R) ^ (K : ℝ) := Real.rpow_pos_of_pos hR1 _
        positivity
      exact le_of_lt (mul_pos hC hpos)
    · -- on the support: the weight is bounded below
      push_neg at h
      have hle : 1 + ‖q.1‖ + q.2 ≤ 1 + R := by linarith
      have hw : (1 + R) ^ (-(K : ℝ)) ≤ (1 + ‖q.1‖ + q.2) ^ (-(K : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hb hle (neg_nonpos.mpr (Nat.cast_nonneg K))
      have hid : (1 + R) ^ (K : ℝ) * (1 + R) ^ (-(K : ℝ)) = 1 := by
        rw [← Real.rpow_add hR1]
        simp
      calc ‖iteratedFDeriv ℝ n f q‖
          ≤ B := hB q
        _ = B * ((1 + R) ^ (K : ℝ) * (1 + R) ^ (-(K : ℝ))) := by rw [hid]; ring
        _ = (B * (1 + R) ^ (K : ℝ)) * (1 + R) ^ (-(K : ℝ)) := by ring
        _ ≤ (B * (1 + R) ^ (K : ℝ)) * (1 + ‖q.1‖ + q.2) ^ (-(K : ℝ)) := by
            refine mul_le_mul_of_nonneg_left hw ?_
            have : (0 : ℝ) < (1 + R) ^ (K : ℝ) := Real.rpow_pos_of_pos hR1 _
            positivity
        _ ≤ (B * (1 + R) ^ (K : ℝ) + 1) * (1 + ‖q.1‖ + q.2) ^ (-(K : ℝ)) := by
            refine mul_le_mul_of_nonneg_right (by linarith) ?_
            exact le_of_lt (Real.rpow_pos_of_pos hb _)

#print axioms admissibleForcing_of_bounded_support

end PF.NavierStokes.FeffermanFaithful

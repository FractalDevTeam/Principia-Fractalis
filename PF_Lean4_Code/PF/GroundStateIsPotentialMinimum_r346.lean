/-
# r346 — `π/(10α)` is the potential's minimum on the computational sector

★ 2026-10-24 — the "supplied coefficient" is a computed spectral quantity ★

## What this repairs

Earlier today I reported, to Pablo and on the board, that the open operator
claim `λ₀(H_α) = π/(10α)` was not a spectral question at all:

> "`π/(10α)` is a hand-supplied COEFFICIENT of `D̂₃`, not an eigenvalue. So the
> open item is not 'compute a spectrum' — it is 'explain why 10 sits in that
> coefficient.'"

The first sentence is true and the conclusion drawn from it was wrong. The
coefficient is supplied, but the VALUE `π/(10α)` is also a computed invariant of
the potential, and this file computes it.

## The computation

`PF/Operators/VAlphaExplicit.lean` defines the arxiv potential diagonally:

    v_alpha_coeff α n = π·D₃(n)/(10α) + ν₂(n)/α + ν₃(n)/α²

where `D₃ = digitalSum3` is the base-3 digit sum and `ν_p = padicValNat p`.
Tabulating the bottom of the diagonal:

    n = 0 :  D₃=0, ν₂=0, ν₃=0  →  0            (proved there: v_alpha_coeff_zero)
    n = 1 :  D₃=1, ν₂=0, ν₃=0  →  π/(10α)      ← groundStateValue
    n = 2 :  D₃=2, ν₂=1, ν₃=0  →  2π/(10α) + 1/α
    n = 3 :  D₃=1, ν₂=0, ν₃=1  →  π/(10α) + 1/α²

So `n = 0` is a zero mode — the trivial/empty state — and on the COMPUTATIONAL
sector `n ≥ 1` the minimum is exactly `π/(10α)`, attained only at `n = 1`.
That is the content below.

## Why the substrate makes this non-accidental

`D₃(n) = 1` is not a generic condition: it says the base-3 expansion of `n` is a
single `1`, i.e. `n` is a power of `3`. The corpus already proves the forward
direction — `digitalSum3_pow3 : digitalSum3 (3^k) = 1`
(`PF/TuringEncoding/D3NonAlgebraic.lean`). And the powers of `3` are exactly the
substrate's dimension tower `H_k = ℂ^(3^k)`.

So the whole tower sits at the minimal digit sum, and the `ν₃` term — the
3-adic valuation, `ν₃(3^k) = k` — is precisely what breaks that degeneracy,
selecting `k = 0`. The potential's minimum on the computational sector is the
BASE of the substrate tower, and the term that picks it out is the one reading
the same prime `3` the substrate is built from.

That is why `π/(10α)` appears bare: `min_{n≥1} D₃(n) = 1`, so the minimum of
the potential is the coupling coefficient times one.

## What is and is not claimed

**Claimed.** For `α > 0`: `groundStateValue α ≤ v_alpha_coeff α n` for every
`n ≥ 1`, with equality exactly at `n = 1`. Equivalently, `π/(10α)` is the
minimum of the arxiv potential's diagonal over the computational sector, and the
minimiser is unique.

**Not claimed.**

1. **`λ₀(H_α) = π/(10α)`.** This is about `V_α`, not `H_α = T + V_α`. The
   kinetic term `T` is a discrete Laplacian and shifts the spectrum; the full
   ground state is NOT computed here and remains open, as does self-adjointness
   of `H_α` — `KatoRellichDischarge.lean` proves the naive bounded formulation
   unsatisfiable by Hellinger–Toeplitz, and `VAlphaPMapShape.lean` moves to the
   `LinearPMap` frame for that reason.
2. **That `10 = h(H₃)` is derived.** `r342` makes `10` a genuine invariant of
   the Coxeter group H₃ (`10 ∣ orderOf` its Coxeter element), but the
   IDENTIFICATION of the coupling's `10` with that invariant is still supplied,
   and still localised to `SubstrateH3IdentificationAtPoincare` in
   `PF/PoincareAlphaDerivedFromH3.lean`.
3. **That `D₃(n) = 1 → n = 3^k`.** Only the converse is used here (and it is
   already in the corpus). Uniqueness of the minimiser is obtained more cheaply,
   from the digit recursion plus `ν₃(n) = 0`, without that characterisation.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic
import PF.Operators.VAlphaExplicit
import PF.TuringEncoding.DigitalSum

namespace PrincipiaTractalis
namespace GroundStateIsPotentialMinimum

open PrincipiaTractalis.Operators
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — The base-3 digit sum is positive off zero -/

/-- **`D₃(n) ≥ 1` for every `n ≠ 0`.**

Via `digitalSum3_eq_digits_sum`: the base-3 digit list of a nonzero `n` is
non-empty and its leading digit is nonzero, so the sum is at least that
digit. -/
theorem digitalSum3_pos {n : ℕ} (hn : n ≠ 0) : 1 ≤ digitalSum3 n := by
  rw [digitalSum3_eq_digits_sum]
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits 3 n).getLast hne ≠ 0 :=
    Nat.getLast_digit_ne_zero 3 hn
  have hmem : (Nat.digits 3 n).getLast hne ∈ Nat.digits 3 n :=
    List.getLast_mem hne
  have hle : (Nat.digits 3 n).getLast hne ≤ (Nat.digits 3 n).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  omega

/-- The digit recursion, in the form needed below: `D₃(n) = n % 3 + D₃(n / 3)`.
Obtained from the corpus's `digitalSum3_add_3_mul` at `x = n % 3`,
`y = n / 3`. -/
theorem digitalSum3_rec (n : ℕ) :
    digitalSum3 n = n % 3 + digitalSum3 (n / 3) := by
  have h := digitalSum3_add_3_mul (x := n % 3) (y := n / 3)
    (Nat.mod_lt _ (by norm_num))
  rwa [Nat.mod_add_div] at h

/-- `D₃(0) = 0`, straight from the definition. -/
theorem digitalSum3_zero' : digitalSum3 0 = 0 := by
  unfold digitalSum3; simp

/-- `D₃(1) = 1`, via the recursion. (The corpus proves this in
`PF/Consciousness/FractalResonance.lean`; it is reproved here so this file
needs no extra import.) -/
theorem digitalSum3_one' : digitalSum3 1 = 1 := by
  rw [digitalSum3_rec]
  norm_num [digitalSum3_zero']

/-- **`D₃(3^k) = 1`** — the substrate tower all sits at the minimal digit sum.

Proved locally by induction through the recursion: `3^(m+1) % 3 = 0` and
`3^(m+1) / 3 = 3^m`, so the digit sum is unchanged going up the tower and
bottoms out at `D₃(1) = 1`. (`PF/TuringEncoding/D3NonAlgebraic.lean` proves
the same statement via the digit list; reproved here to avoid the import.) -/
theorem digitalSum3_pow3' (k : ℕ) : digitalSum3 (3 ^ k) = 1 := by
  induction k with
  | zero => simpa using digitalSum3_one'
  | succ m ih =>
      rw [digitalSum3_rec]
      have h1 : 3 ^ (m + 1) % 3 = 0 := by rw [pow_succ]; omega
      have h2 : 3 ^ (m + 1) / 3 = 3 ^ m := by rw [pow_succ]; omega
      rw [h1, h2, ih]

/-! ## §2 — The lower bound on the computational sector -/

/-- **`groundStateValue α ≤ v_alpha_coeff α n` for `n ≥ 1`.**

`D₃(n) ≥ 1` makes the first term at least `π/(10α)`, and the two valuation
terms are non-negative. -/
theorem groundStateValue_le_v_alpha_coeff {α : ℝ} (hα : 0 < α) {n : ℕ}
    (hn : n ≠ 0) : groundStateValue α ≤ v_alpha_coeff α n := by
  have hD : (1 : ℝ) ≤ d3_coeff n := by
    unfold d3_coeff
    exact_mod_cast digitalSum3_pos hn
  have h2 : (0 : ℝ) ≤ nu2_coeff n := by unfold nu2_coeff; positivity
  have h3 : (0 : ℝ) ≤ nu3_coeff n := by unfold nu3_coeff; positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h10 : (0 : ℝ) < 10 * α := by linarith
  have hsq : (0 : ℝ) < α ^ 2 := by positivity
  unfold groundStateValue v_alpha_coeff
  -- `gcongr` does the monotone division; the numerator step is `π ≤ π · D₃`.
  have hfirst : Real.pi / (10 * α) ≤ Real.pi * d3_coeff n / (10 * α) := by
    gcongr
    nlinarith
  have hrest : (0 : ℝ) ≤ nu2_coeff n / α + nu3_coeff n / α ^ 2 :=
    add_nonneg (div_nonneg h2 hα.le) (div_nonneg h3 hsq.le)
  linarith

/-! ## §3 — The minimiser is unique -/

/-- **Equality forces `n = 1`.**

From equality, each of the three non-negative excesses vanishes: `D₃(n) = 1`,
`ν₂(n) = 0`, `ν₃(n) = 0`. Then `ν₃(n) = 0` with `n ≠ 0` gives `3 ∤ n`, so
`n % 3 ∈ {1, 2}`; the recursion `D₃(n) = n % 3 + D₃(n/3)` rules out `2`, and at
`n % 3 = 1` forces `D₃(n/3) = 0`, hence `n / 3 = 0` by §1, hence `n = 1`. -/
theorem eq_one_of_v_alpha_coeff_eq {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : n ≠ 0)
    (heq : v_alpha_coeff α n = groundStateValue α) : n = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h10 : (0 : ℝ) < 10 * α := by linarith
  have hsq : (0 : ℝ) < α ^ 2 := by positivity
  have hD : (1 : ℝ) ≤ d3_coeff n := by
    unfold d3_coeff; exact_mod_cast digitalSum3_pos hn
  have h2 : (0 : ℝ) ≤ nu2_coeff n := by unfold nu2_coeff; positivity
  have h3 : (0 : ℝ) ≤ nu3_coeff n := by unfold nu3_coeff; positivity
  -- Clear the denominators. Multiplying the equality by `10 * α² > 0` turns
  -- the whole argument linear, which is what the first attempt got wrong by
  -- handing three division-laden goals to `nlinarith`.
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hmul : Real.pi * α * (d3_coeff n - 1)
      + 10 * α * nu2_coeff n + 10 * nu3_coeff n = 0 := by
    unfold groundStateValue v_alpha_coeff at heq
    field_simp at heq
    nlinarith [heq]
  -- the three summands are each non-negative, so each is zero
  have hπα : (0 : ℝ) < Real.pi * α := by positivity
  have t1 : (0 : ℝ) ≤ Real.pi * α * (d3_coeff n - 1) :=
    mul_nonneg hπα.le (by linarith)
  have t2 : (0 : ℝ) ≤ 10 * α * nu2_coeff n :=
    mul_nonneg (by linarith) h2
  have t3 : (0 : ℝ) ≤ 10 * nu3_coeff n := by linarith
  have hv3 : nu3_coeff n = 0 := by linarith
  have ht1 : Real.pi * α * (d3_coeff n - 1) = 0 := by linarith
  have hd : d3_coeff n = 1 := by
    rcases mul_eq_zero.mp ht1 with h | h
    · exact absurd h (ne_of_gt hπα)
    · linarith
  -- translate back to ℕ
  have hdN : digitalSum3 n = 1 := by
    unfold d3_coeff at hd; exact_mod_cast hd
  have hv3N : padicValNat 3 n = 0 := by
    unfold nu3_coeff at hv3; exact_mod_cast hv3
  -- 3 does not divide n
  have hnd : ¬ (3 ∣ n) := by
    intro hdvd
    have : 1 ≤ padicValNat 3 n := one_le_padicValNat_of_dvd hn hdvd
    omega
  have hmod : n % 3 = 1 ∨ n % 3 = 2 := by
    have : n % 3 ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    omega
  rw [digitalSum3_rec] at hdN
  rcases hmod with h | h
  · -- n % 3 = 1 forces D₃(n/3) = 0, so n/3 = 0, so n < 3 and n = 1
    rw [h] at hdN
    have hq : digitalSum3 (n / 3) = 0 := by omega
    have hq0 : n / 3 = 0 := by
      by_contra hc
      have := digitalSum3_pos hc
      omega
    omega
  · rw [h] at hdN
    have := Nat.zero_le (digitalSum3 (n / 3))
    omega

/-! ## §4 — Capstone -/

/-- **★★★ `π/(10α)` is the potential's minimum on the computational sector,
attained uniquely at `n = 1`.**

`n = 0` is excluded because it is a zero mode (`v_alpha_coeff_zero`): the
trivial state, not a computational one.

This is the sense in which the framework's `groundStateValue` is computed rather
than stipulated. It is NOT the ground state of `H_α = T + V_α`; see the file
header's "Not claimed". -/
theorem groundStateValue_is_potential_minimum {α : ℝ} (hα : 0 < α) :
    (∀ n : ℕ, n ≠ 0 → groundStateValue α ≤ v_alpha_coeff α n) ∧
    (v_alpha_coeff α 1 = groundStateValue α) ∧
    (∀ n : ℕ, n ≠ 0 → v_alpha_coeff α n = groundStateValue α → n = 1) := by
  refine ⟨fun n hn => groundStateValue_le_v_alpha_coeff hα hn, ?_,
          fun n hn h => eq_one_of_v_alpha_coeff_eq hα hn h⟩
  unfold v_alpha_coeff groundStateValue d3_coeff nu2_coeff nu3_coeff
  rw [digitalSum3_one']
  simp [padicValNat.one]

/-- **The substrate tower all sits at the minimal digit sum**, and `ν₃` is what
breaks the degeneracy.

`digitalSum3_pow3` (already in the corpus) says every `3^k` has `D₃ = 1`, so the
first term of the potential is `π/(10α)` for the whole tower
`H_k = ℂ^(3^k)`. The `ν₃` term then adds `k/α²`, which is zero exactly at
`k = 0`. Recorded as the structural reason the minimiser is the tower's base. -/
theorem substrate_tower_has_minimal_digitalSum (k : ℕ) :
    d3_coeff (3 ^ k) = 1 := by
  unfold d3_coeff
  rw [digitalSum3_pow3']
  norm_num

end GroundStateIsPotentialMinimum
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.GroundStateIsPotentialMinimum.digitalSum3_pos
#print axioms PrincipiaTractalis.GroundStateIsPotentialMinimum.digitalSum3_pow3'
#print axioms PrincipiaTractalis.GroundStateIsPotentialMinimum.groundStateValue_le_v_alpha_coeff
#print axioms PrincipiaTractalis.GroundStateIsPotentialMinimum.eq_one_of_v_alpha_coeff_eq
#print axioms PrincipiaTractalis.GroundStateIsPotentialMinimum.groundStateValue_is_potential_minimum
#print axioms PrincipiaTractalis.GroundStateIsPotentialMinimum.substrate_tower_has_minimal_digitalSum

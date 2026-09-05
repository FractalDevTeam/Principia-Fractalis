/-
# PF.Numerics.Box0NodePrototype

r331b box 0 midpoint-node prototype — tests the vendored Interval
machinery pattern at ONE actual OPT-40-TIGHT midpoint before generating
530 node certificates.

**Locked prototype node:** `u★ = 49/32 = 1.53125` (exact rational, exact
decimal — no rounding).  This is the 12th (i=11, zero-based) of 23
midpoints in the segment `[3/2, 25/16]`.

**Numerical reference (mpmath dps=60):**

    exp(-π·(49/32))      ≈ 0.008143265
    exp(-π·(49/32))^4    ≈ 4.4·10⁻⁹
    exp(-π·(49/32))^9    ≈ tiny
    omegaPartial 3 (49/32) ≈ 0.008143272

**Certification pattern** (r315 template): `Interval.approx_lt` +
`by approx` + `decide +kernel`.  Decimal literals for Interval values
(r315 convention); rationals for ℝ.

SPDX-License-Identifier: Apache-2.0
-/

import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Sincos
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Interval.Mul
import Interval.Tactic.Approx

namespace PrincipiaTractalis.Box0NodePrototype

open scoped Real

/-! ## §1 — Midpoint identity check -/

theorem midpoint_id :
    (3/2 : ℝ) + (25/16 - 3/2) / 23 * ((11 : ℕ) + 1/2) = 49/32 := by
  norm_num

/-! ## §2 — Single transcendental test at u★ = 49/32 = 1.53125

Tests the vendored Interval package on `exp(-(π · 1.53125))`.  Numerically
≈ 0.00814 < 0.01. -/

theorem exp_neg_pi_u_star_lt :
    Real.exp (-(π * (1.53125 : ℝ))) < (0.01 : ℝ) := by
  refine Interval.approx_lt
    (Interval.exp (-(Interval.pi * (1.53125 : Interval))))
    ((0.01 : Interval))
    (Real.exp (-(π * (1.53125 : ℝ))))
    (0.01 : ℝ)
    (Interval.mem_approx_exp (by approx))
    (by approx)
    ?_
  decide +kernel

/-! ## §3 — Interval mirror for `exp(-π·u) + exp(-π·u)^4 + exp(-π·u)^9`

The expanded form of `omegaPartial 3 u` (via factoring
`exp(-π·k²·u) = exp(-π·u)^(k²)`). -/

noncomputable def omegaPartial3I (U : Interval) : Interval :=
  let E := Interval.exp (-(Interval.pi * U))
  let E2 := E * E
  let E4 := E2 * E2
  E + E4 + E4 * E4 * E

theorem omegaPartial3_at_u_star_lt :
    (Real.exp (-(π * (1.53125 : ℝ)))
       + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
         * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
       + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
         * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
         * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))))
         * Real.exp (-(π * (1.53125 : ℝ))))
      < (0.01 : ℝ) := by
  refine Interval.approx_lt
    (omegaPartial3I (1.53125 : Interval))
    ((0.01 : Interval))
    (Real.exp (-(π * (1.53125 : ℝ)))
       + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
         * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
       + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
         * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
         * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))))
         * Real.exp (-(π * (1.53125 : ℝ))))
    (0.01 : ℝ)
    ?_
    (by approx)
    ?_
  · unfold omegaPartial3I
    approx
  · decide +kernel

/-! ## §4 — `Interval.log`, `Interval.cos`, `Interval.sin` at u★

Tests the remaining transcendental interval functions.  Numerically:

    log(49/32) ≈ 0.4260844
    cos(7.5 · log(49/32)) ≈ -0.9985401
    sin(7.5 · log(49/32)) ≈ -0.0540140

Prove one bound each end-to-end. -/

theorem log_u_star_lt_half : Real.log (1.53125 : ℝ) < (0.5 : ℝ) := by
  refine Interval.approx_lt
    (Interval.log (1.53125 : Interval))
    ((0.5 : Interval))
    (Real.log (1.53125 : ℝ))
    (0.5 : ℝ)
    (Interval.mem_approx_log (by approx))
    (by approx)
    ?_
  decide +kernel

theorem cos_arg_u_star_lt_neg :
    Real.cos ((7.5 : ℝ) * Real.log (1.53125 : ℝ)) < (-0.9 : ℝ) := by
  refine Interval.approx_lt
    (Interval.cos ((7.5 : Interval) * Interval.log (1.53125 : Interval)))
    ((-0.9 : Interval))
    (Real.cos ((7.5 : ℝ) * Real.log (1.53125 : ℝ)))
    (-0.9 : ℝ)
    (Interval.mem_approx_cos (by approx))
    (by approx)
    ?_
  decide +kernel

theorem sin_arg_u_star_lt_zero :
    Real.sin ((7.5 : ℝ) * Real.log (1.53125 : ℝ)) < (0 : ℝ) := by
  refine Interval.approx_lt
    (Interval.sin ((7.5 : Interval) * Interval.log (1.53125 : Interval)))
    ((0 : Interval))
    (Real.sin ((7.5 : ℝ) * Real.log (1.53125 : ℝ)))
    (0 : ℝ)
    (Interval.mem_approx_sin (by approx))
    (by approx)
    ?_
  decide +kernel

/-! ## §5 — Assembled `A · cos · omegaPartial` mirror at u★

At u = 49/32, the three power terms are:
* `P24 = (49/32)^(-3/4)   = exp(log(49/32) · -0.75)` ≈ 0.7265
* `P23 = (49/32)^(-23/32) = exp(log(49/32) · -0.71875)` ≈ 0.7362
* `P25 = (49/32)^(-25/32) = exp(log(49/32) · -0.78125)` ≈ 0.7169

σ-uniform envelopes from §9.7:
* `A_lo := P24 + P25 ≤ P1(σ) + P2(σ) ≤ P23 + P24 =: A_hi`

**Sign semantics at u★:** `C := cos(7.5·log(49/32)) < 0`, `W := omegaPartial 3 (49/32) > 0`.
So `C·W < 0`. Then for the σ-family:

* `Re(σ) = A(σ) · C · W` with `A ∈ [A_lo, A_hi]`, `C·W < 0`
* `Re(σ) ≥ A_hi · C · W` (multiplying `A ≤ A_hi` by negative `C·W` FLIPS inequality)
* `Re(σ) ≤ A_lo · C · W`

Therefore for a σ-uniform Re **LOWER** bound, use **A_hi = P23 + P24**, not A_lo.
For a σ-uniform Re **UPPER** bound (least negative), use A_lo = P24 + P25.

The two scalar tests below exercise the interval machinery on both amplitudes. -/

/-- **Interval mirror using A_lo = P24 + P25** (Re UPPER-bound side, since
`A_lo · C · W` is the LEAST-negative Re value uniformly over σ). -/
noncomputable def box0_re_mirror_Alo (U : Interval) : Interval :=
  let L := Interval.log U
  let E := Interval.exp (-(Interval.pi * U))
  let E2 := E * E
  let E4 := E2 * E2
  let omega := E + E4 + E4 * E4 * E
  let P24 := Interval.exp (L * (-0.75 : Interval))
  let P25 := Interval.exp (L * (-0.78125 : Interval))
  let C := Interval.cos ((7.5 : Interval) * L)
  (P24 + P25) * C * omega

/-- **Interval mirror using A_hi = P23 + P24** (Re LOWER-bound side, since
`A_hi · C · W` is the MOST-negative Re value uniformly over σ). -/
noncomputable def box0_re_mirror_Ahi (U : Interval) : Interval :=
  let L := Interval.log U
  let E := Interval.exp (-(Interval.pi * U))
  let E2 := E * E
  let E4 := E2 * E2
  let omega := E + E4 + E4 * E4 * E
  let P24 := Interval.exp (L * (-0.75 : Interval))
  let P23 := Interval.exp (L * (-0.71875 : Interval))
  let C := Interval.cos ((7.5 : Interval) * L)
  (P23 + P24) * C * omega

/-- Scalar smoke test on the **A_lo** side (Re upper-bound quantity;
NOT the σ-uniform Re lower bound).  Retained to demonstrate the machinery. -/
theorem re_Alo_scalar_at_u_star_gt :
    (Real.exp (Real.log (1.53125 : ℝ) * (-0.75 : ℝ))
      + Real.exp (Real.log (1.53125 : ℝ) * (-0.78125 : ℝ)))
      * Real.cos ((7.5 : ℝ) * Real.log (1.53125 : ℝ))
      * (Real.exp (-(π * (1.53125 : ℝ)))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
             * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))))
           * Real.exp (-(π * (1.53125 : ℝ)))) > (-0.02 : ℝ) := by
  refine Interval.approx_lt
    ((-0.02 : Interval))
    (box0_re_mirror_Alo (1.53125 : Interval))
    (-0.02 : ℝ)
    ((Real.exp (Real.log (1.53125 : ℝ) * (-0.75 : ℝ))
      + Real.exp (Real.log (1.53125 : ℝ) * (-0.78125 : ℝ)))
      * Real.cos ((7.5 : ℝ) * Real.log (1.53125 : ℝ))
      * (Real.exp (-(π * (1.53125 : ℝ)))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
             * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))))
           * Real.exp (-(π * (1.53125 : ℝ)))))
    (by approx)
    ?_
    ?_
  · unfold box0_re_mirror_Alo
    approx
  · decide +kernel

/-- **CORRECT Re LOWER-bound scalar side using A_hi = P23 + P24**.  This is
what feeds the σ-uniform `Re(σ) ≥ -0.02` via §9.7's `box0_pow_sum_ub`. -/
theorem re_Ahi_scalar_at_u_star_gt :
    (Real.exp (Real.log (1.53125 : ℝ) * (-0.71875 : ℝ))
      + Real.exp (Real.log (1.53125 : ℝ) * (-0.75 : ℝ)))
      * Real.cos ((7.5 : ℝ) * Real.log (1.53125 : ℝ))
      * (Real.exp (-(π * (1.53125 : ℝ)))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
             * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))))
           * Real.exp (-(π * (1.53125 : ℝ)))) > (-0.02 : ℝ) := by
  refine Interval.approx_lt
    ((-0.02 : Interval))
    (box0_re_mirror_Ahi (1.53125 : Interval))
    (-0.02 : ℝ)
    ((Real.exp (Real.log (1.53125 : ℝ) * (-0.71875 : ℝ))
      + Real.exp (Real.log (1.53125 : ℝ) * (-0.75 : ℝ)))
      * Real.cos ((7.5 : ℝ) * Real.log (1.53125 : ℝ))
      * (Real.exp (-(π * (1.53125 : ℝ)))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
         + Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ))))
           * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))
             * (Real.exp (-(π * (1.53125 : ℝ))) * Real.exp (-(π * (1.53125 : ℝ)))))
           * Real.exp (-(π * (1.53125 : ℝ)))))
    (by approx)
    ?_
    ?_
  · unfold box0_re_mirror_Ahi
    approx
  · decide +kernel

/-! ## §6 — Non-terminating rational node u† = 1105/736 (Gate B)

Segment `[3/2, 25/16]`, `n = 23`, midpoint index `i = 0`:

    L + (U - L)/n · (i + 1/2)
      = 3/2 + (1/16)/23 · (1/2)
      = 3/2 + 1/736
      = 1105/736.

`736 = 2⁵ · 23`, so `1105/736 = 1.501358695...` is NON-terminating.

Test that the vendored Interval package handles this via `Coe ℚ Interval`
(or `Interval.ofRat`) — no manual outward decimal enclosure needed. -/

theorem midpoint_id_u_dagger :
    (3/2 : ℝ) + (25/16 - 3/2) / 23 * ((0 : ℕ) + 1/2) = 1105/736 := by
  norm_num

/-- Test: `exp(-π · (1105/736)) < 0.01` at the non-terminating rational.
Uses the `ℚ → Interval` coercion. -/
theorem exp_neg_pi_u_dagger_lt :
    Real.exp (-(π * (((1105 : ℚ) / 736 : ℚ) : ℝ))) < (0.01 : ℝ) := by
  refine Interval.approx_lt
    (Interval.exp (-(Interval.pi * (((1105 : ℚ) / 736 : ℚ) : Interval))))
    ((0.01 : Interval))
    (Real.exp (-(π * (((1105 : ℚ) / 736 : ℚ) : ℝ))))
    (0.01 : ℝ)
    (Interval.mem_approx_exp (by approx))
    (by approx)
    ?_
  decide +kernel

end PrincipiaTractalis.Box0NodePrototype

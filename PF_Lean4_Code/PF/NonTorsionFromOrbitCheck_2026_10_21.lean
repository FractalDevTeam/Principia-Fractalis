/-
# PF.NonTorsionFromOrbitCheck_2026_10_21

**Validation of the lift against a known-good instance.** The universal lemma in
`NonTorsionFromOrbit_2026_10_21` compiling proves only that it is well-typed. It
claims to be the *same argument* as the six hand-written per-curve copies, and
that claim is testable: re-derive `E43a1`'s landed capstone
(`E43a1_rank_ge_one`) through the universal route and check it still goes
through, using nothing from `E43a1RankOne_r135` except the genuinely
curve-specific inputs.

What is borrowed from `E43a1RankOne_r135`:

* `P43` — the base point,
* `xs_shifted_infinite` — the height chain's conclusion, which is the real
  mathematical content and stays per-curve,
* `pts_eq_two_pow_smul` — that its doubling chain is the `ℤ`-multiple family.

What is NOT borrowed: `E43a1.X`, `X_pts`, `P_nonTorsion`, and §10's
`E43a1_rank_ge_one`. Those are exactly the parts the universal lemma replaces,
so taking them would make the test circular.

If `E43a1_rank_ge_one_via_universal` below type-checks, the lift is faithful on
the one instance where a hand-written answer already exists to disagree with.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-21.
-/

import PF.NonTorsionFromOrbit_2026_10_21
import PF.E43a1RankOne_r135

namespace PrincipiaTractalis
namespace NonTorsionFromOrbitCheck20261021

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.E43a1RankOne

/-- The universal `X` agrees with `E43a1`'s local copy on every point — they are
the same `match`, so this is `rfl` pointwise. Stated to make the agreement a
checked fact rather than an assumption. -/
theorem X_agrees (Q : E43a1.toAffine.Point) :
    NonTorsionFromOrbit20261021.X Q = PrincipiaTractalis.E43a1RankOne.X Q := by
  cases Q <;> rfl

/-- `E43a1`'s height chain, restated as the universal lemma's hypothesis: the
`x`-coordinates of the `ℤ`-multiple family `2 ^ (n + 4) • P43` are infinite.

This is `xs_shifted_infinite` transported along `pts_eq_two_pow_smul`. The
transport is the only glue the universal route needs per curve. -/
theorem orbit_infinite :
    (Set.range fun n : ℕ =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 4)) • P43)).Infinite := by
  have hfun : (fun n : ℕ =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 4)) • P43))
      = fun n : ℕ => xs (n + 4) := by
    funext n
    rw [← pts_eq_two_pow_smul (n + 4), X_agrees]
    rfl
  rw [hfun]
  exact xs_shifted_infinite

/-- **The lift is faithful: `P43` is non-torsion by the universal route.**
Compare `E43a1RankOne.P_nonTorsion`, which proves the same statement in 24
hand-written lines. -/
theorem P43_nonTorsion_via_universal : ¬ IsOfFinAddOrder P43 :=
  NonTorsionFromOrbit20261021.nonTorsion_of_doubling_orbit_infinite P43 4
    orbit_infinite

/-- **And the landed capstone is reproduced.** `E43a1RankOne.E43a1_rank_ge_one`
is §10 of an 815-line file; this is the same conclusion from the universal
lemma plus the curve's own height chain. -/
theorem E43a1_rank_ge_one_via_universal :
    1 ≤ Module.rank ℤ E43a1.toAffine.Point :=
  NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite P43 4
    orbit_infinite

end NonTorsionFromOrbitCheck20261021
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.NonTorsionFromOrbitCheck20261021.X_agrees
#print axioms PrincipiaTractalis.NonTorsionFromOrbitCheck20261021.orbit_infinite
#print axioms PrincipiaTractalis.NonTorsionFromOrbitCheck20261021.P43_nonTorsion_via_universal
#print axioms PrincipiaTractalis.NonTorsionFromOrbitCheck20261021.E43a1_rank_ge_one_via_universal

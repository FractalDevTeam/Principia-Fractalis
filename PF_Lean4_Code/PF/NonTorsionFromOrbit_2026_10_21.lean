/-
# PF.NonTorsionFromOrbit_2026_10_21

**The non-torsion step, universalised.** Six curve files
(`E37a1`, `E43a1`, `E101a1`, `E106a1`, `E389a1`, `Ch24CurveA`) each define their
own `X : E.toAffine.Point → ℚ` and each re-prove the same ten-line argument:

> if the `x`-coordinates of a family of `ℤ`-multiples of `P` take infinitely
> many values, then `P` has infinite order.

That argument never mentions the curve, the base point, the duplication formula,
or the height machinery. It uses only that `zmultiples P` is finite when `P` is
torsion (mathlib's `IsOfFinAddOrder.finite_zmultiples`) and that a finite set has
finite image. `BSD_91A1_SPEC_2026-10-19` §3b identified it as the **one** part of
the ~815-line per-curve shape that had never been lifted, and §4 item 1 assigned
the lift.

What this file does NOT do: it does not prove any point is non-torsion. It
converts "the x-orbit is infinite" into "the point is non-torsion", and
"infinite x-orbit" is still supplied per curve by the height-window chain
(`DuplicationHeightUniversal_r176` + the per-curve doubling chain). The
hypothesis is the real content and it stays where it was.

Stated for an arbitrary index family `f : ℕ → ℤ` rather than for `2 ^ n`
specifically, which costs nothing and covers the shifted families the per-curve
files actually use (`E43a1` fires at `fun n => (2 : ℤ) ^ (n + 4)`, because its
height threshold only bites from `16 • P` on).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-21.
-/

import PF.MordellWeilRankLowerBound_r129

namespace PrincipiaTractalis
namespace NonTorsionFromOrbit20261021

open PrincipiaTractalis.MordellWeilRankLowerBound
open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-! ## §1 — the x-coordinate projection, once -/

/-- **The `x`-coordinate of an affine point**, with the identity sent to `0`.

The value at `zero` is arbitrary and never used: every lemma below only ever
reads `X` on points of the form `f n • P`, and the conclusions are about the
*range* of those values being infinite, which no single sentinel can affect. -/
def X : W.Point → F
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

@[simp] theorem X_zero : X (0 : W.Point) = 0 := rfl

@[simp] theorem X_some {x y : F} (h : W.Nonsingular x y) :
    X (@Point.some _ _ W x y h) = x := rfl

/-! ## §2 — infinite x-orbit ⇒ infinite order -/

/-- **The universal non-torsion step.** If the `x`-coordinates of the
`ℤ`-multiples `f n • P` take infinitely many values, `P` is not torsion.

Proof shape, unchanged from the six hand-written copies: a torsion `P` has
finite `zmultiples`, so the image of that finite set under `X` is finite; but
every `X (f n • P)` lies in that image, so the hypothesised infinite range
would be a subset of a finite set. -/
theorem nonTorsion_of_X_range_infinite (P : W.Point) (f : ℕ → ℤ)
    (hinf : (Set.range fun n => X (f n • P)).Infinite) :
    ¬ IsOfFinAddOrder P := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => X (f n • P))
      ⊆ X '' (AddSubgroup.zmultiples P : Set W.Point) := by
    rintro q ⟨n, rfl⟩
    exact ⟨f n • P, AddSubgroup.mem_zmultiples_iff.mpr ⟨f n, rfl⟩, rfl⟩
  exact hinf ((hfinite.image X).subset hsub)

/-- The same, specialised to the doubling orbit `2 ^ n • P` with an offset —
the shape every per-curve file actually fires, since the height threshold only
bites from some `2 ^ k • P` onwards. -/
theorem nonTorsion_of_doubling_orbit_infinite (P : W.Point) (k : ℕ)
    (hinf : (Set.range fun n => X (((2 : ℤ) ^ (n + k)) • P)).Infinite) :
    ¬ IsOfFinAddOrder P :=
  nonTorsion_of_X_range_infinite P (fun n => (2 : ℤ) ^ (n + k)) hinf

/-! ## §3 — straight to the rank, for the per-curve capstones -/

/-- **Rank ≥ 1 from an infinite x-orbit**, composing with r129. This is the
whole tail of a per-curve rank file: given the height chain's infinitude, the
flag follows with no further curve input. -/
theorem rank_ge_one_of_X_range_infinite (P : W.Point) (f : ℕ → ℤ)
    (hinf : (Set.range fun n => X (f n • P)).Infinite) :
    1 ≤ Module.rank ℤ W.Point :=
  mordellWeil_rank_ge_one W P (nonTorsion_of_X_range_infinite P f hinf)

/-- The doubling-orbit form of the rank conclusion. -/
theorem rank_ge_one_of_doubling_orbit_infinite (P : W.Point) (k : ℕ)
    (hinf : (Set.range fun n => X (((2 : ℤ) ^ (n + k)) • P)).Infinite) :
    1 ≤ Module.rank ℤ W.Point :=
  mordellWeil_rank_ge_one W P (nonTorsion_of_doubling_orbit_infinite P k hinf)

/-- And the r129 certificate, for callers that want its name. -/
theorem certificate_of_X_range_infinite (P : W.Point) (f : ℕ → ℤ)
    (hinf : (Set.range fun n => X (f n • P)).Infinite) :
    NonTorsionCertificate W P :=
  nonTorsion_of_X_range_infinite P f hinf

end NonTorsionFromOrbit20261021
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.NonTorsionFromOrbit20261021.nonTorsion_of_X_range_infinite
#print axioms PrincipiaTractalis.NonTorsionFromOrbit20261021.nonTorsion_of_doubling_orbit_infinite
#print axioms PrincipiaTractalis.NonTorsionFromOrbit20261021.rank_ge_one_of_X_range_infinite
#print axioms PrincipiaTractalis.NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite
#print axioms PrincipiaTractalis.NonTorsionFromOrbit20261021.certificate_of_X_range_infinite

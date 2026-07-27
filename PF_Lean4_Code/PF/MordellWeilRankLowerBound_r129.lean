/-
# PF.MordellWeilRankLowerBound_r129

★★★ 2026-07-27 — THE FIRST REAL STONE ON THE BSD AXIS ★★★

The 2026-07-27 audit established that the corpus's "rank-equality contract"
(`BSDCapstoneTypedBridgeV4`) is `rfl` between two aliases of one hand-written
lookup table: no `Module.rank` is ever evaluated, no L-function exists. The
honest definition (`MordellWeilRank`, `PF/AlgebraicGeometry/MordellWeilGroup.lean`)
is never proven for any curve.

This file starts the honest arc. It proves, for a general elliptic curve point
group, the conversion lemma

  non-torsion point  ⟹  1 ≤ Module.rank ℤ E(ℚ)

so that every future non-torsion certificate (Lutz–Nagell, reduction-injectivity,
or explicit-multiple computation) immediately yields a kernel-verified rank
lower bound — the first half of `MordellWeilRankIs E n` for the rank ≥ 1 curves
of the 17-curve cohort.

Mathematics: a point `P` of infinite order gives an injective ℤ-linear map
`ℤ →ₗ[ℤ] E.Point`, `n ↦ n • P`; ranks are monotone under injective linear maps
and `Module.rank ℤ ℤ = 1`.

HONEST SCOPE. This is the conversion lemma only. It does NOT certify any
specific point as non-torsion (that requires Lutz–Nagell or torsion-injection
under reduction, absent from mathlib v4.24 and from this corpus), and it gives
lower bounds only — upper bounds require Mordell–Weil finiteness plus descent,
which mathlib does not yet have (M. Stoll's height/descent pipeline is in
progress upstream as of 2026). Stated for any `AddCommGroup` so it applies to
`WeierstrassCurve.Affine.Point` over any field.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`, no project
axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-27.
-/
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import PF.AlgebraicGeometry.MordellWeilGroup

namespace PrincipiaTractalis.MordellWeilRankLowerBound

open WeierstrassCurve

/-! ## §1 — the general conversion lemma -/

/-- A point of infinite additive order in any abelian group `M` gives an
injective ℤ-linear map `ℤ →ₗ[ℤ] M`. -/
noncomputable def zsmulHom {M : Type*} [AddCommGroup M] (P : M) : ℤ →ₗ[ℤ] M where
  toFun n := n • P
  map_add' m n := add_zsmul P m n
  map_smul' m n := by simp [mul_zsmul]

theorem zsmulHom_injective {M : Type*} [AddCommGroup M] {P : M}
    (hP : ¬ IsOfFinAddOrder P) : Function.Injective (zsmulHom P) := by
  intro m n hmn
  by_contra hne
  have hsub : (m - n) • P = 0 := by
    have h' : m • P = n • P := hmn
    rw [sub_zsmul, h']
    simp
  have hzero : m - n ≠ 0 := sub_ne_zero.mpr hne
  exact hP (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m - n, hzero, hsub⟩)

/-- **The conversion lemma.** Any abelian group containing a point of infinite
order has ℤ-rank at least 1. -/
theorem one_le_rank_of_infinite_order {M : Type*} [AddCommGroup M] (P : M)
    (hP : ¬ IsOfFinAddOrder P) : 1 ≤ Module.rank ℤ M := by
  have h := LinearMap.lift_rank_le_of_injective (zsmulHom P) (zsmulHom_injective hP)
  rwa [Module.rank_self ℤ, Cardinal.lift_one, Cardinal.lift_uzero] at h

/-! ## §2 — specialization to elliptic curves -/

/-- **Non-torsion point ⟹ Mordell–Weil rank ≥ 1**, for the affine point group
of any Weierstrass curve over any field.  This is the target shape for the
rank-1 cohort (37a1, 43a1, …, 106a1): each needs only a non-torsion
certificate for its recorded Heegner-derived point. -/
theorem mordellWeil_rank_ge_one {F : Type*} [Field F] [DecidableEq F] (W : Affine F)
    (P : W.Point) (hP : ¬ IsOfFinAddOrder P) :
    1 ≤ Module.rank ℤ W.Point :=
  one_le_rank_of_infinite_order P hP

/-! ## §3 — what remains, stated as the honest open interface

The corpus's per-curve statement is `MordellWeilRankIs E n`
(`PF/AlgebraicGeometry/MordellWeilRankAgreement17.lean`).  The missing input
for §2 to fire on a specific curve is exactly this Prop: -/

/-- The open certificate: `P` has infinite order in `E(ℚ)`.  Discharging this
for one explicit point of one explicit curve (via Lutz–Nagell or
torsion-injection under good reduction — neither yet in mathlib v4.24) is the
next stone.  Nothing in this file pretends it is discharged. -/
def NonTorsionCertificate {F : Type*} [Field F] [DecidableEq F] (W : Affine F) (P : W.Point) : Prop :=
  ¬ IsOfFinAddOrder P

/-- The conditional per-curve consequence, with the open certificate as an
explicit hypothesis — the honest replacement shape for the lookup-table
"discharge". -/
theorem rank_ge_one_under_certificate {F : Type*} [Field F] [DecidableEq F] (W : Affine F)
    (P : W.Point) (h : NonTorsionCertificate W P) :
    1 ≤ Module.rank ℤ W.Point :=
  mordellWeil_rank_ge_one W P h

end PrincipiaTractalis.MordellWeilRankLowerBound

#print axioms PrincipiaTractalis.MordellWeilRankLowerBound.one_le_rank_of_infinite_order
#print axioms PrincipiaTractalis.MordellWeilRankLowerBound.mordellWeil_rank_ge_one

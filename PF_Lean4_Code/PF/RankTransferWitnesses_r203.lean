/-
# PF.RankTransferWitnesses_r203

★★★ 2026-08-05 — THE PER-CURVE CERTIFICATES, RE-DERIVED THROUGH THE MACHINE ★★★

r202 built the universal rank pipeline.  r154 and r169 proved, by hand and
per curve, that 389a1 has rank ≥ 2 and 5077a1 has rank ≥ 3.  This stone
runs the *old certificates* through the *new machine*: the two rank flags
come out of `RankPipelineUniversal`, with the already-certified interval
arithmetic (`regDet_pos`, `regDet3_pos`) as the only numerical input.
Nothing is recomputed.

The one thing that had to be built is the **bridge**.  The universal layer
speaks `canheightW` — r171's generic `canheight` over r177's `lognh ∘ X`
(r199's universal x-projection, r176's `nh`).  The per-curve layer speaks
`CanonicalHeight389a1.canheight` — the same limit, but over
`Real.log (naiveHeight ∘ X)` with r143's per-curve `X` and r130's
`naiveHeight`.  They are the same function; the file proves it:

* `X_bridge_389` / `X_bridge_5077` — the universal x-projection is the
  per-curve one (`cases`-then-`rfl`: the two pattern matches agree);
* `lognh_bridge_389` / `lognh_bridge_5077` — the two log-height helpers
  agree, via r199's `naiveHeight_eq_nh` cast;
* `canheightW_eq_389` / `canheightW_eq_5077` — the two canonical heights
  agree.  These are `funext` + `rfl`: once the height helpers are equal as
  *functions*, the two `hseq`s and hence the two `limUnder`s are
  definitionally the same.  The universal and per-curve layers line up
  exactly, with no analytic re-argument;
* `pairingW_eq_389` / `pairingW_eq_5077` — immediate corollaries.

Then:

* `E389a1_rank_ge_two_universal` — r202's `rank_ge_two_universal` at the
  389a1 hypothesis package (r202 §4) and r154's `regDet_pos`;
* `E5077a1_rank_ge_three_universal` — r202's `rank_ge_universal` at
  `n = 3`, with the 5077a1 hypothesis package proved here (§C.1: the
  b-invariants of `⟨0,0,1,−7,6⟩`, `Disc = 5077`, and 2-torsion-freeness
  from r166b), r202's `gram_det_fin_three`, and r169's `regDet3_pos`.

HONEST SCOPE.  Two rank *lower* bounds, already known, re-derived through
a curve-independent pipeline.  No new numerics, no new curve, no BSD, and
nothing about `L(E, s)`.  What is new is that the per-curve height towers
(r147–r154, r156–r169) are no longer load-bearing for these two flags: the
universal chain r171–r202 carries them, and the per-curve files contribute
only their certified determinants.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-05.
-/
import PF.RankPipelineUniversal_r202
import PF.E389a1RankTwo_r154
import PF.E5077a1RankThree_r169
import PF.TorsionTrivial5077a1_r166b

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.RankTransferWitnesses

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationLogWindow
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.CanheightParallelogramUniversal
open PrincipiaTractalis.GramRankGeneral
open PrincipiaTractalis.RankPipelineUniversal
open WeierstrassCurve WeierstrassCurve.Affine
open Filter Topology

/-! ## §A — the 389a1 bridge -/

section Bridge389

open PrincipiaTractalis.E389a1RankOne (E389a1)

/-- r199's universal x-projection, specialised to 389a1, is r143's. -/
theorem X_bridge_389 (S : E389a1.toAffine.Point) :
    PointParallelogramUniversal.X S = E389a1RankOne.X S := by
  cases S <;> rfl

/-- **A.1 — the log-height bridge.**  r177's `lognh` on r199's universal
`X` is r147's per-curve `lognh`. -/
theorem lognh_bridge_389 (S : E389a1.toAffine.Point) :
    lognh (PointParallelogramUniversal.X S) = CanonicalHeight389a1.lognh S := by
  rw [X_bridge_389]
  simp only [DuplicationLogWindow.lognh, CanonicalHeight389a1.lognh]
  congr 1
  exact_mod_cast
    (PointParallelogramUniversal.naiveHeight_eq_nh (E389a1RankOne.X S)).symm

/-- The two height helpers are equal *as functions* — this is what makes
the two `hseq`s, hence the two limits, definitionally the same. -/
theorem lognhX_eq_389 :
    (fun R : E389a1.toAffine.Point => lognh (PointParallelogramUniversal.X R))
      = CanonicalHeight389a1.lognh :=
  funext lognh_bridge_389

/-- **A.2 — the canonical heights agree.** -/
theorem canheightW_eq_389 (R : E389a1.toAffine.Point) :
    canheightW E389a1.toAffine R = CanonicalHeight389a1.canheight R := by
  show canheight
      (fun S : E389a1.toAffine.Point => lognh (PointParallelogramUniversal.X S)) R = _
  rw [lognhX_eq_389]
  rfl

/-- **A.3 — the pairings agree.** -/
theorem pairingW_eq_389 (P Q : E389a1.toAffine.Point) :
    pairingW E389a1.toAffine P Q = CanheightParallelogram389a1.pairing P Q := by
  simp only [pairingW, CanheightParallelogram389a1.pairing, canheightW_eq_389]

end Bridge389

/-! ## §B — 389a1 end-to-end through the universal machine -/

section Rank389

open PrincipiaTractalis.E389a1RankOne (E389a1 P389_nonsingular)
open PrincipiaTractalis.E389a1RankTwo (Q389 regDet_pos)

/-- r152's certified `regDet`, transported to the universal pairing. -/
theorem regW_ne_zero_389 :
    canheightW E389a1.toAffine (Point.some P389_nonsingular)
        * canheightW E389a1.toAffine Q389
      - pairingW E389a1.toAffine (Point.some P389_nonsingular) Q389 ^ 2 ≠ 0 := by
  have hd : RegulatorIndependence389a1.regDet (Point.some P389_nonsingular) Q389 ≠ 0 :=
    ne_of_gt regDet_pos
  simp only [RegulatorIndependence389a1.regDet] at hd
  rw [canheightW_eq_389, canheightW_eq_389, pairingW_eq_389]
  exact hd

/-- **★★★ B — `rank E389a1(ℚ) ≥ 2`, through the universal pipeline. ★★★**

The hypothesis package is r202 §4; the numerical input is r154's
`regDet_pos`, transported by §A.  No 389a1-specific height estimate
appears anywhere in the chain. -/
theorem E389a1_rank_ge_two_universal :
    (2 : Cardinal) ≤ Module.rank ℤ E389a1.toAffine.Point :=
  rank_ge_two_universal h389_b₂ h389_b₄ h389_b₆ h389_b₈ h389_hΔ h389_2tor
    (Point.some P389_nonsingular) Q389 regW_ne_zero_389

end Rank389

/-! ## §C — 5077a1: hypothesis package, bridge, flag

5077a1 has no `Universal5077a1` file, so §C.1 proves its hypothesis
package here, mirroring r180's for 389a1. -/

section Curve5077

open PrincipiaTractalis.E5077a1RankOne (E5077a1)

/-! ### §C.1 — the hypothesis package for `E5077a1 = ⟨0, 0, 1, −7, 6⟩` -/

theorem h5077_b₂ : (E5077a1.toAffine).b₂ = ((0 : ℤ) : ℚ) := by
  norm_num [WeierstrassCurve.b₂, E5077a1]

theorem h5077_b₄ : (E5077a1.toAffine).b₄ = ((-14 : ℤ) : ℚ) := by
  norm_num [WeierstrassCurve.b₄, E5077a1]

theorem h5077_b₆ : (E5077a1.toAffine).b₆ = ((25 : ℤ) : ℚ) := by
  norm_num [WeierstrassCurve.b₆, E5077a1]

theorem h5077_b₈ : (E5077a1.toAffine).b₈ = ((-49 : ℤ) : ℚ) := by
  norm_num [WeierstrassCurve.b₈, E5077a1]

/-- The discriminant of 5077a1, from the b-invariants. -/
theorem disc_5077a1 : Disc 0 (-14) 25 (-49) = 5077 := by decide

theorem h5077_hΔ : Disc 0 (-14) 25 (-49) ≠ 0 := by
  rw [disc_5077a1]; decide

/-- 5077a1 has no rational 2-torsion: `2 • R = 0` with `R ≠ 0` would make
`R` a torsion point, and r166b proved the torsion subgroup trivial. -/
theorem h5077_2tor : ∀ R : (E5077a1.toAffine).Point, R ≠ 0 → (2 : ℕ) • R ≠ 0 := by
  intro R hR h2
  exact hR (TorsionTrivial5077a1.torsion_eq_zero
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, h2⟩))

/-! ### §C.2 — the 5077a1 bridge -/

/-- r199's universal x-projection, specialised to 5077a1, is r144's. -/
theorem X_bridge_5077 (S : E5077a1.toAffine.Point) :
    PointParallelogramUniversal.X S = E5077a1RankOne.X S := by
  cases S <;> rfl

theorem lognh_bridge_5077 (S : E5077a1.toAffine.Point) :
    lognh (PointParallelogramUniversal.X S) = CanonicalHeight5077a1.lognh S := by
  rw [X_bridge_5077]
  simp only [DuplicationLogWindow.lognh, CanonicalHeight5077a1.lognh]
  congr 1
  exact_mod_cast
    (PointParallelogramUniversal.naiveHeight_eq_nh (E5077a1RankOne.X S)).symm

theorem lognhX_eq_5077 :
    (fun R : E5077a1.toAffine.Point => lognh (PointParallelogramUniversal.X R))
      = CanonicalHeight5077a1.lognh :=
  funext lognh_bridge_5077

theorem canheightW_eq_5077 (R : E5077a1.toAffine.Point) :
    canheightW E5077a1.toAffine R = CanonicalHeight5077a1.canheight R := by
  show canheight
      (fun S : E5077a1.toAffine.Point => lognh (PointParallelogramUniversal.X S)) R = _
  rw [lognhX_eq_5077]
  rfl

theorem pairingW_eq_5077 (P Q : E5077a1.toAffine.Point) :
    pairingW E5077a1.toAffine P Q = CanheightParallelogram5077a1.pairing P Q := by
  simp only [pairingW, CanheightParallelogram5077a1.pairing, canheightW_eq_5077]

/-! ### §C.3 — the 3×3 Gram determinant is r168's `regDet3` -/

section Rank5077

open PrincipiaTractalis.E5077a1RankThree (Pt Qt Rt regDet3_pos)

/-- r202's 3×3 expansion, rearranged into r168's `regDet3`. -/
theorem gram_det_eq_regDet3 :
    (gram (pairingW E5077a1.toAffine) ![Pt, Qt, Rt]).det
      = Regulator3Independence5077a1.regDet3 Pt Qt Rt := by
  rw [gram_det_fin_three h5077_b₂ h5077_b₄ h5077_b₆ h5077_b₈ h5077_hΔ h5077_2tor]
  simp only [Regulator3Independence5077a1.regDet3, canheightW_eq_5077,
    pairingW_eq_5077]
  ring

/-- **★★★ C — `rank E5077a1(ℚ) ≥ 3`, through the universal pipeline. ★★★**

The hypothesis package is §C.1; the numerical input is r169's
`regDet3_pos`, transported by §C.2. -/
theorem E5077a1_rank_ge_three_universal :
    (3 : Cardinal) ≤ Module.rank ℤ E5077a1.toAffine.Point := by
  have h := rank_ge_universal (n := 3) h5077_b₂ h5077_b₄ h5077_b₆ h5077_b₈
    h5077_hΔ h5077_2tor ![Pt, Qt, Rt]
    (by rw [gram_det_eq_regDet3]; exact ne_of_gt regDet3_pos)
  simpa using h

end Rank5077

end Curve5077

end PrincipiaTractalis.RankTransferWitnesses

#print axioms PrincipiaTractalis.RankTransferWitnesses.lognh_bridge_389
#print axioms PrincipiaTractalis.RankTransferWitnesses.canheightW_eq_389
#print axioms PrincipiaTractalis.RankTransferWitnesses.pairingW_eq_389
#print axioms PrincipiaTractalis.RankTransferWitnesses.E389a1_rank_ge_two_universal
#print axioms PrincipiaTractalis.RankTransferWitnesses.h5077_2tor
#print axioms PrincipiaTractalis.RankTransferWitnesses.lognh_bridge_5077
#print axioms PrincipiaTractalis.RankTransferWitnesses.canheightW_eq_5077
#print axioms PrincipiaTractalis.RankTransferWitnesses.pairingW_eq_5077
#print axioms PrincipiaTractalis.RankTransferWitnesses.gram_det_eq_regDet3
#print axioms PrincipiaTractalis.RankTransferWitnesses.E5077a1_rank_ge_three_universal

/-
# PF.AlgebraicGeometry.MordellWeilRankAgreement17_V4Readings

★★★★★ 2026-06-07 — BRIDGE 3 PHASE 1 ★★★★★

Per-curve axiom-free V4 readings for the 11 remaining curves in
`MordellWeilRankAgreement17`. Each theorem proves
`algebraicRankV4 E_X = n_X` by unfolding `manuscriptRankV4` and
chaining `if_neg`/`if_pos` past every preceding case-split branch,
using `congrArg WeierstrassCurve.aᵢ` + `simp` on a discriminating
coefficient field per pair.

Combined with the 6 already-axiom-free V4 readings in
`MordellWeilRankAgreement17`, this raises the §2 axiom-free
V4-reading count from 6/17 → 17/17.

HONEST SCOPE: this is purely a typed-residual cleanup pass.
It does NOT change the bridge's literal scope — the
`MordellWeilRankIs E n` residuals (literal `Module.rank ℤ
E.toAffine.Point = n`) remain typed published-theorem
hypotheses (Coates-Wiles, Gross-Zagier, Kolyvagin, BSZ 2014)
because mathlib lacks Mordell-Weil rank infrastructure.

ZERO project axioms, kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-07.
-/

import PF.AlgebraicGeometry.MordellWeilRankAgreement17

namespace PF.AlgebraicGeometry.MordellWeilRankAgreement17

open PrincipiaTractalis
open PrincipiaTractalis.BSDGaloisPairConcordance
open PrincipiaTractalis.BSDRankThreeCurveFramework
open PrincipiaTractalis.BSD_MultiCMRankZeroBatch
open PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE53a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE61a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE79a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE83a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE89a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE101a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1
open PrincipiaTractalis.BSD_HeegnerRank1ProofE106a1
open PrincipiaTractalis.BSD_Rank2AttemptE389a1
open PF.Referee.BSDCapstoneTypedBridgeV4

/-! ## §1 — V4 reading for E_43a1 (rank 1)

Coefficients (a₁, a₂, a₃, a₄, a₆) = (0, 1, 1, 0, 0).
Preceding case-splits: E_rank_zero, E_36a1, E_49a1, E_121b1, E_144a1, E_rank_one. -/

theorem algebraicRankV4_E_43a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 ≠ E_rank_zero := by
    intro heq
    have := congrArg WeierstrassCurve.a₂ heq
    simp only [PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1, E_rank_zero] at this; norm_num at this
  have h1 : PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 ≠ E_36a1 := by
    intro heq
    have := congrArg WeierstrassCurve.a₂ heq
    simp only [PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1, E_36a1] at this; norm_num at this
  have h2 : PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 ≠ E_49a1 := by
    intro heq
    have := congrArg WeierstrassCurve.a₁ heq
    simp only [PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1, E_49a1] at this; norm_num at this
  have h3 : PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 ≠ E_121b1 := by
    intro heq
    have := congrArg WeierstrassCurve.a₂ heq
    simp only [PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1, E_121b1] at this; norm_num at this
  have h4 : PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 ≠ E_144a1 := by
    intro heq
    have := congrArg WeierstrassCurve.a₂ heq
    simp only [PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1, E_144a1] at this; norm_num at this
  have h5 : PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 ≠ E_rank_one := by
    intro heq
    have := congrArg WeierstrassCurve.a₂ heq
    simp only [PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1, E_rank_one] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos rfl]

/-! ## §2 — V4 reading for E_53a1 (rank 1)

Coefficients = (1, -1, 1, 0, 0). All preceding curves distinguishable by a₁ (1 vs 0)
except E_49a1 (a₁ = 1 too — discriminate by a₃: 1 vs 0). -/

theorem algebraicRankV4_E_53a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE53a1.E_53a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_53a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_53a1, E_rank_zero] at this; norm_num at this
  have h1 : E_53a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_53a1, E_36a1] at this; norm_num at this
  have h2 : E_53a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq
    simp only [E_53a1, E_49a1] at this; norm_num at this
  have h3 : E_53a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_53a1, E_121b1] at this; norm_num at this
  have h4 : E_53a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_53a1, E_144a1] at this; norm_num at this
  have h5 : E_53a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_53a1, E_rank_one] at this; norm_num at this
  have h6 : E_53a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_53a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_pos rfl]

/-! ## §3 — V4 reading for E_61a1 (rank 1)

Coefficients = (1, 0, 0, -2, 1). -/

theorem algebraicRankV4_E_61a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE61a1.E_61a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_61a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_61a1, E_rank_zero] at this; norm_num at this
  have h1 : E_61a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_61a1, E_36a1] at this; norm_num at this
  have h2 : E_61a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_61a1, E_49a1] at this; norm_num at this
  have h3 : E_61a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_61a1, E_121b1] at this; norm_num at this
  have h4 : E_61a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_61a1, E_144a1] at this; norm_num at this
  have h5 : E_61a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_61a1, E_rank_one] at this; norm_num at this
  have h6 : E_61a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_61a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_61a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_61a1, E_53a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_pos rfl]

/-! ## §4 — V4 reading for E_79a1 (rank 1)

Coefficients = (1, 1, 1, -2, 0). -/

theorem algebraicRankV4_E_79a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE79a1.E_79a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_79a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_79a1, E_rank_zero] at this; norm_num at this
  have h1 : E_79a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_79a1, E_36a1] at this; norm_num at this
  have h2 : E_79a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_79a1, E_49a1] at this; norm_num at this
  have h3 : E_79a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_79a1, E_121b1] at this; norm_num at this
  have h4 : E_79a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_79a1, E_144a1] at this; norm_num at this
  have h5 : E_79a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_79a1, E_rank_one] at this; norm_num at this
  have h6 : E_79a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_79a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_79a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_79a1, E_53a1] at this; norm_num at this
  have h8 : E_79a1 ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_79a1, E_61a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_pos rfl]

/-! ## §5 — V4 reading for E_83a1 (rank 1)

Coefficients = (1, 1, 1, 1, 0). -/

theorem algebraicRankV4_E_83a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE83a1.E_83a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_83a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_83a1, E_rank_zero] at this; norm_num at this
  have h1 : E_83a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_83a1, E_36a1] at this; norm_num at this
  have h2 : E_83a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_83a1, E_49a1] at this; norm_num at this
  have h3 : E_83a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_83a1, E_121b1] at this; norm_num at this
  have h4 : E_83a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_83a1, E_144a1] at this; norm_num at this
  have h5 : E_83a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_83a1, E_rank_one] at this; norm_num at this
  have h6 : E_83a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_83a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_83a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_83a1, E_53a1] at this; norm_num at this
  have h8 : E_83a1 ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_83a1, E_61a1] at this; norm_num at this
  have h9 : E_83a1 ≠ E_79a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq; simp only [E_83a1, E_79a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_pos rfl]

/-! ## §6 — V4 reading for E_89a1 (rank 1)

Coefficients = (1, 1, 1, -1, 0). -/

theorem algebraicRankV4_E_89a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE89a1.E_89a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_89a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_89a1, E_rank_zero] at this; norm_num at this
  have h1 : E_89a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_89a1, E_36a1] at this; norm_num at this
  have h2 : E_89a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_89a1, E_49a1] at this; norm_num at this
  have h3 : E_89a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_89a1, E_121b1] at this; norm_num at this
  have h4 : E_89a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_89a1, E_144a1] at this; norm_num at this
  have h5 : E_89a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_89a1, E_rank_one] at this; norm_num at this
  have h6 : E_89a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_89a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_89a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_89a1, E_53a1] at this; norm_num at this
  have h8 : E_89a1 ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_89a1, E_61a1] at this; norm_num at this
  have h9 : E_89a1 ≠ E_79a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq; simp only [E_89a1, E_79a1] at this; norm_num at this
  have h10 : E_89a1 ≠ E_83a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq; simp only [E_89a1, E_83a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_pos rfl]

/-! ## §7 — V4 reading for E_101a1 (rank 1)

Coefficients = (0, 1, 1, -1, -1). a₁ = 0 so cannot use a₁ discriminator
against the 7 preceding curves with a₁ = 1. Use a₂ instead. -/

theorem algebraicRankV4_E_101a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE101a1.E_101a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_101a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_101a1, E_rank_zero] at this; norm_num at this
  have h1 : E_101a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_101a1, E_36a1] at this; norm_num at this
  have h2 : E_101a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_101a1, E_49a1] at this; norm_num at this
  have h3 : E_101a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_101a1, E_121b1] at this; norm_num at this
  have h4 : E_101a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_101a1, E_144a1] at this; norm_num at this
  have h5 : E_101a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_101a1, E_rank_one] at this; norm_num at this
  have h6 : E_101a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq
    simp only [E_101a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_101a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_101a1, E_53a1] at this; norm_num at this
  have h8 : E_101a1 ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_101a1, E_61a1] at this; norm_num at this
  have h9 : E_101a1 ≠ E_79a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_101a1, E_79a1] at this; norm_num at this
  have h10 : E_101a1 ≠ E_83a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_101a1, E_83a1] at this; norm_num at this
  have h11 : E_101a1 ≠ E_89a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_101a1, E_89a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, if_pos rfl]

/-! ## §8 — V4 reading for E_102a1 (rank 1)

Coefficients = (1, 1, 0, -2, 0). -/

theorem algebraicRankV4_E_102a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1.E_102a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_102a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_102a1, E_rank_zero] at this; norm_num at this
  have h1 : E_102a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_102a1, E_36a1] at this; norm_num at this
  have h2 : E_102a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_102a1, E_49a1] at this; norm_num at this
  have h3 : E_102a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_102a1, E_121b1] at this; norm_num at this
  have h4 : E_102a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_102a1, E_144a1] at this; norm_num at this
  have h5 : E_102a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_102a1, E_rank_one] at this; norm_num at this
  have h6 : E_102a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_102a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_102a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_102a1, E_53a1] at this; norm_num at this
  have h8 : E_102a1 ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_102a1, E_61a1] at this; norm_num at this
  have h9 : E_102a1 ≠ E_79a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_102a1, E_79a1] at this; norm_num at this
  have h10 : E_102a1 ≠ E_83a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_102a1, E_83a1] at this; norm_num at this
  have h11 : E_102a1 ≠ E_89a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_102a1, E_89a1] at this; norm_num at this
  have h12 : E_102a1 ≠ E_101a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_102a1, E_101a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11,
      if_neg h12, if_pos rfl]

/-! ## §9 — V4 reading for E_106a1 (rank 1)

Coefficients = (1, 1, 0, -7, 5). -/

theorem algebraicRankV4_E_106a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_HeegnerRank1ProofE106a1.E_106a1 = 1 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_106a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_106a1, E_rank_zero] at this; norm_num at this
  have h1 : E_106a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_106a1, E_36a1] at this; norm_num at this
  have h2 : E_106a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_106a1, E_49a1] at this; norm_num at this
  have h3 : E_106a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_106a1, E_121b1] at this; norm_num at this
  have h4 : E_106a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_106a1, E_144a1] at this; norm_num at this
  have h5 : E_106a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_106a1, E_rank_one] at this; norm_num at this
  have h6 : E_106a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq
    simp only [E_106a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_106a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_106a1, E_53a1] at this; norm_num at this
  have h8 : E_106a1 ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_106a1, E_61a1] at this; norm_num at this
  have h9 : E_106a1 ≠ E_79a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_106a1, E_79a1] at this; norm_num at this
  have h10 : E_106a1 ≠ E_83a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_106a1, E_83a1] at this; norm_num at this
  have h11 : E_106a1 ≠ E_89a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_106a1, E_89a1] at this; norm_num at this
  have h12 : E_106a1 ≠ E_101a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_106a1, E_101a1] at this; norm_num at this
  have h13 : E_106a1 ≠ E_102a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq; simp only [E_106a1, E_102a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11,
      if_neg h12, if_neg h13, if_pos rfl]

/-! ## §10 — V4 reading for E_389a1 (rank 2)

Coefficients = (0, 1, 1, -2, 0). -/

theorem algebraicRankV4_E_389a1 :
    algebraicRankV4 PrincipiaTractalis.BSD_Rank2AttemptE389a1.E_389a1 = 2 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_389a1 ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_389a1, E_rank_zero] at this; norm_num at this
  have h1 : E_389a1 ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_389a1, E_36a1] at this; norm_num at this
  have h2 : E_389a1 ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_49a1] at this; norm_num at this
  have h3 : E_389a1 ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_389a1, E_121b1] at this; norm_num at this
  have h4 : E_389a1 ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_389a1, E_144a1] at this; norm_num at this
  have h5 : E_389a1 ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_389a1, E_rank_one] at this; norm_num at this
  have h6 : E_389a1 ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq
    simp only [E_389a1, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_389a1 ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_53a1] at this; norm_num at this
  have h8 : E_389a1 ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_61a1] at this; norm_num at this
  have h9 : E_389a1 ≠ E_79a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_79a1] at this; norm_num at this
  have h10 : E_389a1 ≠ E_83a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_83a1] at this; norm_num at this
  have h11 : E_389a1 ≠ E_89a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_89a1] at this; norm_num at this
  have h12 : E_389a1 ≠ E_101a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq; simp only [E_389a1, E_101a1] at this; norm_num at this
  have h13 : E_389a1 ≠ E_102a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_102a1] at this; norm_num at this
  have h14 : E_389a1 ≠ E_106a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_389a1, E_106a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11,
      if_neg h12, if_neg h13, if_neg h14, if_pos rfl]

/-! ## §11 — V4 reading for E_rank_three (rank 3)

Coefficients = (0, 0, 1, -7, 6). LMFDB 5077.a1. -/

theorem algebraicRankV4_E_rank_three :
    algebraicRankV4 E_rank_three = 3 := by
  unfold algebraicRankV4 manuscriptRankV4
  have h0 : E_rank_three ≠ E_rank_zero := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_rank_three, E_rank_zero] at this; norm_num at this
  have h1 : E_rank_three ≠ E_36a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_rank_three, E_36a1] at this; norm_num at this
  have h2 : E_rank_three ≠ E_49a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_49a1] at this; norm_num at this
  have h3 : E_rank_three ≠ E_121b1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_rank_three, E_121b1] at this; norm_num at this
  have h4 : E_rank_three ≠ E_144a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₃ heq; simp only [E_rank_three, E_144a1] at this; norm_num at this
  have h5 : E_rank_three ≠ E_rank_one := by
    intro heq; have := congrArg WeierstrassCurve.a₄ heq; simp only [E_rank_three, E_rank_one] at this; norm_num at this
  have h6 : E_rank_three ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq
    simp only [E_rank_three, PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1] at this; norm_num at this
  have h7 : E_rank_three ≠ E_53a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_53a1] at this; norm_num at this
  have h8 : E_rank_three ≠ E_61a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_61a1] at this; norm_num at this
  have h9 : E_rank_three ≠ E_79a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_79a1] at this; norm_num at this
  have h10 : E_rank_three ≠ E_83a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_83a1] at this; norm_num at this
  have h11 : E_rank_three ≠ E_89a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_89a1] at this; norm_num at this
  have h12 : E_rank_three ≠ E_101a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_rank_three, E_101a1] at this; norm_num at this
  have h13 : E_rank_three ≠ E_102a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_102a1] at this; norm_num at this
  have h14 : E_rank_three ≠ E_106a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₁ heq; simp only [E_rank_three, E_106a1] at this; norm_num at this
  have h15 : E_rank_three ≠ E_389a1 := by
    intro heq; have := congrArg WeierstrassCurve.a₂ heq; simp only [E_rank_three, E_389a1] at this; norm_num at this
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11,
      if_neg h12, if_neg h13, if_neg h14, if_neg h15, if_pos rfl]

/-! ## §12 — Combined: AllSeventeenV4ReadingsKnown is AXIOM-FREE -/

/-- **★★★ ALL 17 V4 READINGS AXIOM-FREE ★★★** —
    `AllSeventeenV4ReadingsKnown` is now discharged axiom-free.
    This raises §2's axiom-free V4-reading count from 6/17 → 17/17. -/
theorem allSeventeenV4ReadingsKnown_axiom_free :
    AllSeventeenV4ReadingsKnown :=
  ⟨algebraicRankV4_E_rank_zero,
   algebraicRankV4_E_36a1,
   algebraicRankV4_E_49a1,
   algebraicRankV4_E_121b1,
   algebraicRankV4_E_144a1,
   algebraicRankV4_E_rank_one,
   algebraicRankV4_E_43a1,
   algebraicRankV4_E_53a1,
   algebraicRankV4_E_61a1,
   algebraicRankV4_E_79a1,
   algebraicRankV4_E_83a1,
   algebraicRankV4_E_89a1,
   algebraicRankV4_E_101a1,
   algebraicRankV4_E_102a1,
   algebraicRankV4_E_106a1,
   algebraicRankV4_E_389a1,
   algebraicRankV4_E_rank_three⟩

end PF.AlgebraicGeometry.MordellWeilRankAgreement17

-- Axiom checks
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_43a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_53a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_61a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_79a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_83a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_89a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_101a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_102a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_106a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_389a1
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.algebraicRankV4_E_rank_three
#print axioms PF.AlgebraicGeometry.MordellWeilRankAgreement17.allSeventeenV4ReadingsKnown_axiom_free

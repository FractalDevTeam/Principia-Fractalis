/-
# RightEdgeSigns_2026_10_08 — the right-edge sign reduction, and a repair of
#   the two "already landed" edge theorems

## What this file does, in one paragraph

`PF/Analytic/RectangleLogBranch_r331g.lean:707`
(`rectangleIntegral'_logDeriv_eq_of_right_edge_chain`) stands on **seven**
hypotheses: bottom edge, top edge, and five right-edge segments spanning
`t ∈ [-15,15]`. `codex/RH_BELOW_15_ROUTE_2026-10-01.md` §6 and §C2 say that only
**three** of these are primitive numerical obligations — R1, R2, R3 on
`t ∈ [0,15]` — the negative-`t` segments being conjugate mirrors and bottom/top
being already proved. §C3 of that same document records that the three transfer
lemmas needed to actually *perform* that reduction (`im_reflect`, `re_conj_t`,
`im_conj_t`) **are missing**, so no Lean statement in the corpus yet carries the
reduced hypothesis count. This file supplies them and performs the reduction:
`rectangleIntegral'_logDeriv_eq_of_three_right_edge_facts` takes exactly R1, R2,
R3 in the natural (unrotated) form of the route document's §6 table and concludes
`RectangleIntegral' (logDeriv ξ) zF wF = 2`.

**Seven standing hypotheses become three.** No sign fact is proved here that was
not already in the corpus; what is new is the symmetry layer and the repair below.

## ★ DEFECT FOUND AND REPAIRED BY ADDITION ★

`r331g`'s header, and `codex/RH_BELOW_15_ROUTE_2026-10-01.md` §1 and §6, both
report the bottom and top edges as **done**, citing
`PF/Analytic/RiemannXiTopEdge_r331c.lean:76` (`top_edge_neg_xi_re_pos`) and
`PF/Analytic/RiemannXiBottomEdgeAtMinus15_r331d.lean:87`
(`bottom_edge_neg_xi_re_pos`). Measured 2026-10-08:

* **Neither module has ever produced an olean.**
  `.lake/build/lib/lean/PF/Analytic/RiemannXiTopEdge_r331c.olean` and
  `...RiemannXiBottomEdgeAtMinus15_r331d.olean` do not exist, while
  `RiemannXiTopUnion.olean` (their expensive dependency, the 4,241-panel union)
  *is* current.
* **`r331c` does not elaborate.** `lake env lean` on it exits 1 with eight
  errors. Root cause: the file imports `RiemannXiTopUnion` and
  `RiemannXiSymmetries_r326` and opens only
  `PrincipiaTractalis.RiemannXiSymmetries`, but `riemannXiEntire` is declared in
  `PrincipiaTractalis.RiemannXiEntire` (`RiemannXiEntire_r325.lean:81`). Opening
  a namespace does not re-export what *that* namespace opened, so the identifier
  fails to resolve and **`autoImplicit` silently binds it as a fresh implicit
  variable of an unknown sort**. Every statement in `r331c` therefore quantifies
  over an arbitrary `riemannXiEntire : Sort u`, and `#print axioms` on
  `top_edge_re_neg_full`, `top_edge_neg_xi_re_pos` and `top_edge_ne_zero` returns
  `[propext, sorryAx, Classical.choice, Quot.sound]`.
* `r331d` fails upstream of its own content: it imports `r331c`, whose olean does
  not exist.

This is a second live instance of the defect class
`codex/AUTOIMPLICIT_CAPTURE_SCAN_2026-10-01.md` describes. That scan returned a
negative result, but it indexed only the 71 α / H₃ constants and states its own
limitation explicitly: "a capture of some unrelated name elsewhere would not be
caught by this scan." `riemannXiEntire` is such a name, and the capture sits on
the RH critical path.

**The repair here is additive, not a downgrade.** The mathematics `r331c`
intended is sound and its dependency is genuinely kernel-clean:
`PrincipiaTractalis.RiemannXiTopUnion.top15_re_lt_neg_1e4` (`RiemannXiTopUnion.lean:76`,
`σ ∈ [1/2,1]` at `t = 15`) returns exactly
`[propext, Classical.choice, Quot.sound]`. §1 and §2 below reconstruct
`re_reflect`, the full-segment top edge, and the bottom edge **about the real
`riemannXiEntire`**, under `set_option autoImplicit false` so the capture cannot
recur. `r331c`/`r331d` are left untouched; the standing fix for them is one
`import PF.Analytic.RiemannXiEntire_r325` plus one
`open PrincipiaTractalis.RiemannXiEntire`, which is another lane's edit.

## What is still open after this file

Exactly the three facts of the route document's §6 table, on the line `σ = 1`:

| name | claim | `t`-interval | rotation `ω` | numeric margin (mpmath, not certified) |
|---|---|---|---|---|
| R1 | `0 < Re ξ(1+it)` | `[0,13]` | `1` | `+2.50941e-3` at `t=13` |
| R2 | `0 < Im ξ(1+it)` | `[13,29/2]` | `-I` | `+4.14183e-4` at `t=29/2` |
| R3 | `Re ξ(1+it) < 0` | `[29/2,15]` | `-1` | `-5.59104e-4` at `t=29/2` |

None is proved here and none is provable at this pin without new certified
numerics: the 4,241 panels are hard-wired to `t = 15`
(`RH_BELOW_15_ROUTE_2026-10-01.md` §7), and the consumer layer for `t`-boxed
enclosures (`RiemannXiEdgeEnclosure_r331c.lean`, `EdgeReEnclosure:66`,
`EdgeImEnclosure:72`) has no producer. `ξ(1) = 1/2` (`r328:110`) makes R1 true at
the single point `t = 0`, which does not discharge a segment.

## Honesty notes

* **No new sign fact.** §3's reduction is pure symmetry; §1–§2 re-derive, for the
  real `ξ`, facts whose only numerical input is `top15_re_lt_neg_1e4`.
* **No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`, no
  True-equivalent existential.** Every theorem below is a universally quantified
  inequality or an equation between complex numbers.
* **`autoImplicit` is switched off for this file**, which is why the capture that
  silently broke `r331c` cannot happen here.
* **Nothing existing is edited.** This file only adds.

## mathlib dependencies, each verified to exist at the pin
### (`eed770a43495`, Lean v4.24.0-rc1)

| name | file:line |
|---|---|
| `Complex.ext` | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.conj_re`, `Complex.conj_im` | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.mul_re` | `Mathlib/Data/Complex/Basic.lean` |
| `Set.uIcc_of_le` | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` |
| `Set.mem_Icc` | `Mathlib/Order/Interval/Set/Defs.lean` |

## Corpus dependencies

* `PF/Analytic/RectangleLogBranch_r331g.lean:707` —
  `rectangleIntegral'_logDeriv_eq_of_right_edge_chain`, and `zF`/`wF` at `:542,:546`.
* `PF/Analytic/RiemannXiTopUnion.lean:76` — `top15_re_lt_neg_1e4`
  (olean current, kernel-clean, measured).
* `PF/Analytic/RiemannXiEntire_r325.lean:81` — `riemannXiEntire`
  (imported transitively through r331g; **opened explicitly here**, which is the
  line `r331c` is missing).
* `PF/Analytic/RiemannXiSymmetries_r326.lean:88,109` — `riemannXiEntire_conj`,
  `riemannXiEntire_reflect_vertical`.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RectangleLogBranch_r331g
import PF.Analytic.RiemannXiTopUnion

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RightEdgeSigns20261008

open Complex
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RectangleLogBranchR331g
open scoped ComplexConjugate

noncomputable section

/-! ## §0 — The four rotated real parts, once

`r331g` consumes its hypotheses in the rotated shape `0 < (ω * ξ s).re`. These
four identities are the dictionary between that shape and the natural statements
`0 < Re ξ`, `Re ξ < 0`, `0 < Im ξ`, `Im ξ < 0`. -/

lemma re_one_mul (z : ℂ) : ((1 : ℂ) * z).re = z.re := by
  simp

lemma re_neg_one_mul (z : ℂ) : ((-1 : ℂ) * z).re = -z.re := by
  simp

lemma re_neg_I_mul (z : ℂ) : ((-I) * z).re = z.im := by
  simp [Complex.mul_re]

lemma re_I_mul (z : ℂ) : (I * z).re = -z.im := by
  simp [Complex.mul_re]

/-! ## §1 — Repair: the top edge, about the real `ξ`

This is the content `PF/Analytic/RiemannXiTopEdge_r331c.lean` intended. It is
reconstructed here because that file's `riemannXiEntire` is an `autoImplicit`
capture (see the header), so its theorems are `sorryAx`-tainted statements about
an arbitrary value. The numerical input is unchanged:
`RiemannXiTopUnion.top15_re_lt_neg_1e4` on `σ ∈ [1/2,1]`. -/

/-- **Reflection transfers the real part across `σ ↦ 1 - σ`.**
(`r331c:53`'s `re_reflect`, correctly scoped.) -/
theorem re_reflect (σ t : ℝ) :
    (riemannXiEntire (⟨σ, t⟩ : ℂ)).re = (riemannXiEntire (⟨1 - σ, t⟩ : ℂ)).re := by
  rw [riemannXiEntire_reflect_vertical σ t, Complex.conj_re]

/-- **`Re ξ(σ + 15i) < -1/10000` on the FULL segment `σ ∈ [0,1]`.**
r331b/`RiemannXiTopUnion` gives `[1/2,1]`; r326's vertical reflection gives
`[0,1/2]`. (`r331c:64`'s `top_edge_re_neg_full`, correctly scoped.) -/
theorem top_edge_re_neg_full {σ : ℝ} (h0 : (0 : ℝ) ≤ σ) (h1 : σ ≤ 1) :
    (riemannXiEntire (⟨σ, 15⟩ : ℂ)).re < -(1/10000 : ℝ) := by
  rcases le_or_gt (1/2 : ℝ) σ with hσ | hσ
  · exact RiemannXiTopUnion.top15_re_lt_neg_1e4 hσ h1
  · have hlo : (1/2 : ℝ) ≤ 1 - σ := by linarith
    have hhi : (1 : ℝ) - σ ≤ 1 := by linarith
    have h := RiemannXiTopUnion.top15_re_lt_neg_1e4 hlo hhi
    rwa [← re_reflect σ 15] at h

/-- **The top edge in the rotated shape r331g's `hTop` wants.**
(`r331c:76`'s `top_edge_neg_xi_re_pos`, correctly scoped and pre-rotated.) -/
theorem top_edge_rotated {σ : ℝ} (h0 : (0 : ℝ) ≤ σ) (h1 : σ ≤ 1) :
    0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, 15⟩ : ℂ)).re := by
  rw [re_neg_one_mul]
  have h := top_edge_re_neg_full h0 h1
  linarith

/-! ## §2 — Repair: the bottom edge, about the real `ξ`

`PF/Analytic/RiemannXiBottomEdgeAtMinus15_r331d.lean` cannot elaborate at all:
it imports `r331c`, whose olean does not exist. Its own derivation — conjugation
in `t` plus §1 — is sound and is reproduced here. -/

/-- **`(σ - ti) = conj (σ + ti)`.** The `t`-conjugation `r331d:60` has only at
`t = 15`; stated here for every `t`, which is what §3 needs. -/
lemma mk_neg_im_eq_conj (σ t : ℝ) : (⟨σ, -t⟩ : ℂ) = conj (⟨σ, t⟩ : ℂ) := by
  apply Complex.ext
  · simp [Complex.conj_re]
  · simp [Complex.conj_im]

/-- **★ The general `t`-conjugation of ξ ★** — `ξ(σ - ti) = conj (ξ(σ + ti))`.
This is the lemma `RH_BELOW_15_ROUTE_2026-10-01.md` §C3 lists as missing
(`re_conj_t`/`im_conj_t` in one statement); `r331d:69`'s `re_conj_at_neg_15` is
the `t = 15`, real-part-only special case. Everything in §3 runs on this. -/
theorem xi_mk_neg_im (σ t : ℝ) :
    riemannXiEntire (⟨σ, -t⟩ : ℂ) = conj (riemannXiEntire (⟨σ, t⟩ : ℂ)) := by
  rw [mk_neg_im_eq_conj σ t, riemannXiEntire_conj]

/-- **`re_conj_t`** — the real part of ξ is even in `t`. -/
theorem re_xi_mk_neg_im (σ t : ℝ) :
    (riemannXiEntire (⟨σ, -t⟩ : ℂ)).re = (riemannXiEntire (⟨σ, t⟩ : ℂ)).re := by
  rw [xi_mk_neg_im σ t, Complex.conj_re]

/-- **`im_conj_t`** — the imaginary part of ξ is odd in `t`. -/
theorem im_xi_mk_neg_im (σ t : ℝ) :
    (riemannXiEntire (⟨σ, -t⟩ : ℂ)).im = -(riemannXiEntire (⟨σ, t⟩ : ℂ)).im := by
  rw [xi_mk_neg_im σ t, Complex.conj_im]

/-- **`Re ξ(σ - 15i) < -1/10000` on `σ ∈ [0,1]`.**
(`r331d:79`'s `bottom_edge_re_neg_full`, correctly scoped.) -/
theorem bottom_edge_re_neg_full {σ : ℝ} (h0 : (0 : ℝ) ≤ σ) (h1 : σ ≤ 1) :
    (riemannXiEntire (⟨σ, -15⟩ : ℂ)).re < -(1/10000 : ℝ) := by
  rw [show (-15 : ℝ) = -(15 : ℝ) by norm_num, re_xi_mk_neg_im σ 15]
  exact top_edge_re_neg_full h0 h1

/-- **The bottom edge in the rotated shape r331g's `hBot` wants.**
(`r331d:87`'s `bottom_edge_neg_xi_re_pos`, correctly scoped and pre-rotated.) -/
theorem bottom_edge_rotated {σ : ℝ} (h0 : (0 : ℝ) ≤ σ) (h1 : σ ≤ 1) :
    0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, -15⟩ : ℂ)).re := by
  rw [re_neg_one_mul]
  have h := bottom_edge_re_neg_full h0 h1
  linarith

/-! ## §3 — The reduction: seven hypotheses become three

The three primitive facts, in the natural unrotated form of the route document's
§6 table. Each is a statement about the right edge `σ = 1` at **non-negative**
`t` only; §3 supplies the `t < 0` halves and the two horizontal edges. -/

/-- R1 — `0 < Re ξ(1 + it)` on `t ∈ [0,13]`. **Open.** -/
def RightEdgeR1 : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 13, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re

/-- R2 — `0 < Im ξ(1 + it)` on `t ∈ [13,29/2]`. **Open.** -/
def RightEdgeR2 : Prop :=
  ∀ t ∈ Set.Icc (13 : ℝ) (29/2), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im

/-- R3 — `Re ξ(1 + it) < 0` on `t ∈ [29/2,15]`. **Open.** -/
def RightEdgeR3 : Prop :=
  ∀ t ∈ Set.Icc (29/2 : ℝ) 15, (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0

/-- Segment `t ∈ [-15,-29/2]`, rotation `-1`: the mirror of R3. -/
theorem hR1_of_R3 (hR3 : RightEdgeR3) :
    ∀ t ∈ Set.uIcc (-15 : ℝ) (-29/2),
      0 < ((-1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (-15 : ℝ) ≤ -29/2), Set.mem_Icc] at ht
  obtain ⟨htlo, hthi⟩ := ht
  have hmem : -t ∈ Set.Icc (29/2 : ℝ) 15 := by
    rw [Set.mem_Icc]; constructor <;> linarith
  have h := hR3 (-t) hmem
  rw [re_neg_one_mul, show t = -(-t) by ring, re_xi_mk_neg_im 1 (-t)]
  linarith

/-- Segment `t ∈ [-29/2,-13]`, rotation `+I`: the mirror of R2. The rotation
flips, exactly as `RH_BELOW_15_ROUTE_2026-10-01.md` §C3 warns, because
conjugation negates `Im`. -/
theorem hR2_of_R2 (hR2 : RightEdgeR2) :
    ∀ t ∈ Set.uIcc (-29/2 : ℝ) (-13),
      0 < (I * riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (-29/2 : ℝ) ≤ -13), Set.mem_Icc] at ht
  obtain ⟨htlo, hthi⟩ := ht
  have hmem : -t ∈ Set.Icc (13 : ℝ) (29/2) := by
    rw [Set.mem_Icc]; constructor <;> linarith
  have h := hR2 (-t) hmem
  rw [re_I_mul, show t = -(-t) by ring, im_xi_mk_neg_im 1 (-t)]
  linarith

/-- Segment `t ∈ [-13,13]`, rotation `1`: R1 on `t ≥ 0`, its mirror on `t < 0`. -/
theorem hR3_of_R1 (hR1 : RightEdgeR1) :
    ∀ t ∈ Set.uIcc (-13 : ℝ) 13,
      0 < ((1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (-13 : ℝ) ≤ 13), Set.mem_Icc] at ht
  obtain ⟨htlo, hthi⟩ := ht
  rw [re_one_mul]
  rcases le_or_gt (0 : ℝ) t with ht0 | ht0
  · exact hR1 t (by rw [Set.mem_Icc]; exact ⟨ht0, hthi⟩)
  · have hmem : -t ∈ Set.Icc (0 : ℝ) 13 := by
      rw [Set.mem_Icc]; constructor <;> linarith
    have h := hR1 (-t) hmem
    rw [show t = -(-t) by ring, re_xi_mk_neg_im 1 (-t)]
    linarith

/-- Segment `t ∈ [13,29/2]`, rotation `-I`: R2 itself, rotated. -/
theorem hR4_of_R2 (hR2 : RightEdgeR2) :
    ∀ t ∈ Set.uIcc (13 : ℝ) (29/2),
      0 < ((-I) * riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (13 : ℝ) ≤ 29/2), Set.mem_Icc] at ht
  rw [re_neg_I_mul]
  exact hR2 t (by rw [Set.mem_Icc]; exact ht)

/-- Segment `t ∈ [29/2,15]`, rotation `-1`: R3 itself, rotated. -/
theorem hR5_of_R3 (hR3 : RightEdgeR3) :
    ∀ t ∈ Set.uIcc (29/2 : ℝ) 15,
      0 < ((-1 : ℂ) * riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (29/2 : ℝ) ≤ 15), Set.mem_Icc] at ht
  rw [re_neg_one_mul]
  have h := hR3 t (by rw [Set.mem_Icc]; exact ht)
  linarith

/-- Bottom edge, in r331g's `hBot` shape, from §2 — **no longer a hypothesis**. -/
theorem hBot_discharged :
    ∀ σ ∈ Set.uIcc (0 : ℝ) 1, 0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, -15⟩ : ℂ)).re := by
  intro σ hσ
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hσ
  exact bottom_edge_rotated hσ.1 hσ.2

/-- Top edge, in r331g's `hTop` shape, from §1 — **no longer a hypothesis**. -/
theorem hTop_discharged :
    ∀ σ ∈ Set.uIcc (0 : ℝ) 1, 0 < ((-1 : ℂ) * riemannXiEntire (⟨σ, 15⟩ : ℂ)).re := by
  intro σ hσ
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hσ
  exact top_edge_rotated hσ.1 hσ.2

/-- **★★★ The reduction ★★★** — `RectangleIntegral' (logDeriv ξ) zF wF = 2`
from **three** hypotheses, not seven. The two horizontal edges are discharged by
§1–§2 (numerical input: the 4,241-panel union at `t = 15`), and the two
negative-`t` right-edge segments plus the negative half of `[-13,13]` are
discharged by §2's `t`-conjugation. What is left standing is precisely the
route document's §6 table. -/
theorem rectangleIntegral'_logDeriv_eq_of_three_right_edge_facts
    (hR1 : RightEdgeR1) (hR2 : RightEdgeR2) (hR3 : RightEdgeR3) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF = (2 : ℂ) :=
  rectangleIntegral'_logDeriv_eq_of_right_edge_chain
    hBot_discharged hTop_discharged
    (hR1_of_R3 hR3) (hR2_of_R2 hR2) (hR3_of_R1 hR1) (hR4_of_R2 hR2) (hR5_of_R3 hR3)

/-- The same statement with the three facts spelled out inline, for callers that
would rather not unfold the `Prop` abbreviations. -/
theorem rectangleIntegral'_logDeriv_eq_two_of_right_edge
    (hR1 : ∀ t ∈ Set.Icc (0 : ℝ) 13, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR2 : ∀ t ∈ Set.Icc (13 : ℝ) (29/2), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im)
    (hR3 : ∀ t ∈ Set.Icc (29/2 : ℝ) 15, (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF = (2 : ℂ) :=
  rectangleIntegral'_logDeriv_eq_of_three_right_edge_facts hR1 hR2 hR3

end

/-! ## Axiom check -/

#print axioms re_reflect
#print axioms top_edge_re_neg_full
#print axioms top_edge_rotated
#print axioms xi_mk_neg_im
#print axioms re_xi_mk_neg_im
#print axioms im_xi_mk_neg_im
#print axioms bottom_edge_re_neg_full
#print axioms bottom_edge_rotated
#print axioms hR1_of_R3
#print axioms hR2_of_R2
#print axioms hR3_of_R1
#print axioms hR4_of_R2
#print axioms hR5_of_R3
#print axioms hBot_discharged
#print axioms hTop_discharged
#print axioms rectangleIntegral'_logDeriv_eq_of_three_right_edge_facts
#print axioms rectangleIntegral'_logDeriv_eq_two_of_right_edge

end RightEdgeSigns20261008
end PrincipiaTractalis

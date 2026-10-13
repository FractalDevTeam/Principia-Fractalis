/-
# RightEdgeSignsProof_2026_10_09 — the right-edge sign REDUCTION LAYER
#   (the non-numerical half of the missing t-boxed producer)

## What this file does, in one paragraph

`PF/Analytic/RightEdgeSigns_2026_10_08.lean` reduced the seven standing
half-plane hypotheses of the rectangle bridge to **three** genuinely-open facts
on the right edge `σ = 1`:

  R1 : `∀ t ∈ [0,13],    0 < (ξ(1+it)).re`
  R2 : `∀ t ∈ [13,29/2], 0 < (ξ(1+it)).im`
  R3 : `∀ t ∈ [29/2,15], (ξ(1+it)).re < 0`

`codex/RH_BELOW_15_ROUTE_2026-10-01.md` §3 and §9 name two things that must
exist before those three can be discharged by certified numerics:

  (a) a **finite-subdivision chaining lemma** — turn a finite cover of a closed
      `t`-interval by consecutive sub-boxes, each carrying the sign, into the
      sign on the whole interval; and
  (b) a **t-boxed interval-quadrature producer** — emit, per sub-box, a certified
      enclosure of `completedRiemannZeta₀(1+it)` (`EdgeReEnclosure`/
      `EdgeImEnclosure`, `RiemannXiEdgeEnclosure_r331c`), with `t` ranging.

This file supplies (a) in full, and the exact per-box bridge from an enclosure to
a sign (the glue that sits between r331c's structures and R1/R2/R3). It does NOT
and CANNOT supply (b): no certified `t`-boxed enclosure of `Λ₀` exists at this pin
(the 4,241 panels are hard-wired to `t = 15`, route §7). **Therefore none of
R1/R2/R3 is proved here, and `riemannHypothesis_below_15` stays conditional on
R1 ∧ R2 ∧ R3.** What is new and kernel-clean:

* `re_xi_edge` / `im_xi_edge` — the exact `σ = 1` closed forms, as standalone
  proved identities (r331c's header states them in prose; it does not prove them
  as reusable lemmas).
* `forall_Icc_cover` — the finite-subdivision chaining lemma of route §3/§9,
  as a general real-analysis fact (any `P`, any closed interval, any finite cover).
* `R1_box` / `R2_box` / `R3_box` — per-sub-box: `EdgeReEnclosure` +
  `EdgeImEnclosure` + a producer-supplied interval inequality ⟹ the box sign.
  These are the precise obligations a producer must fill.
* `R1_of_cover` / `R2_of_cover` / `R3_of_cover` — assemble the whole segment from
  a finite chain of box signs; their conclusions are *syntactically* the R1/R2/R3
  that `rectangleIntegral'_logDeriv_eq_two_of_right_edge` consumes.
* `R1_at_zero` / `re_xi_edge_zero` / `R3_at_fifteen` — the two segment ENDPOINTS
  that are already certified: `Re ξ(1) = 1/2` exactly (so R1 holds at `t = 0`),
  and `Re ξ(1+15i) < 0` from the panel union (so R3 holds at `t = 15`). These are
  single points; they do NOT discharge the open segments.

## Honesty notes

* **No new sign fact over any positive-length segment.** Nothing here closes an
  open piece of R1, R2 or R3. The endpoints are two isolated points.
* **The producer is the whole remaining distance.** `R1_box`/`R2_box`/`R3_box`
  each take an `EdgeReEnclosure`/`EdgeImEnclosure` hypothesis; not one such
  instance exists at the pin with `t` ranging, and building them is the
  40,000–60,000-module campaign of route §9 — months of compute, not a lemma.
* **r331c's §4 upper-bound consumers are NOT in its olean.** Measured
  2026-10-09: `#check re_xi_upper_bound_from_edge` against the loaded
  `RiemannXiEdgeEnclosure_r331c.olean` (built 2026-09-08) is
  `unknownIdentifier`; the source §4 was added after that build and the module
  was never re-elaborated. So R3's bridge here is derived directly from
  `re_xi_at_s`, not from r331c §4, and depends on nothing stale.
* **No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.** Every result
  is a proved identity, a proved reduction, or a proved sign at a point.
* **`autoImplicit` is off** for this file.
* **Additive.** Nothing existing is edited.

## Dependencies, each with a current olean (measured 2026-10-09)
* `PF/Analytic/RiemannXiEdgeEnclosure_r331c.lean` — `EdgeReEnclosure`,
  `EdgeImEnclosure` (§1); transitively `re_xi_at_s`, `im_xi_at_s`
  (`RiemannXiThetaBoxEnclosure_r331a`), `riemannXiEntire` (`RiemannXiEntire_r325`).
* `PF/Analytic/RiemannXiTopUnion.lean:76` — `top15_re_lt_neg_1e4`
  (kernel-clean, `σ ∈ [1/2,1]` at `t = 15`), for the R3 endpoint only.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiEdgeEnclosure_r331c
import PF.Analytic.RiemannXiTopUnion

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RightEdgeSignsProof20261009

open Complex
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.RiemannXiEdgeEnclosure

noncomputable section

/-! ## §0 — The exact `σ = 1` closed forms

Specialising `re_xi_at_s` / `im_xi_at_s` (r331a, general in σ and t) to `σ = 1`,
where `σ(σ-1) - t² = -t²` and `t(2σ-1) = t`. These are exact identities, not
enclosures; every downstream box lemma rewrites with them. -/

/-- `Re ξ(1+it) = (1 - t²·Re Λ₀(1+it) - t·Im Λ₀(1+it)) / 2`. -/
theorem re_xi_edge (t : ℝ) :
    (riemannXiEntire (⟨1, t⟩ : ℂ)).re
      = (1 - t ^ 2 * (completedRiemannZeta₀ (⟨1, t⟩ : ℂ)).re
           - t * (completedRiemannZeta₀ (⟨1, t⟩ : ℂ)).im) / 2 := by
  rw [re_xi_at_s]; ring

/-- `Im ξ(1+it) = (-t²·Im Λ₀(1+it) + t·Re Λ₀(1+it)) / 2`. -/
theorem im_xi_edge (t : ℝ) :
    (riemannXiEntire (⟨1, t⟩ : ℂ)).im
      = (-t ^ 2 * (completedRiemannZeta₀ (⟨1, t⟩ : ℂ)).im
           + t * (completedRiemannZeta₀ (⟨1, t⟩ : ℂ)).re) / 2 := by
  rw [im_xi_at_s]; ring

/-! ## §1 — The two certified segment endpoints

Honest scope: these are two isolated points, the shared corners of the right-edge
traversal. They do NOT discharge any open segment; they only confirm R1 and R3 are
consistent with what is already kernel-proved at their endpoints. -/

/-- `Re ξ(1) = 1/2` exactly (the `t = 0` corner; `ξ(1) = 1/2`). -/
theorem re_xi_edge_zero : (riemannXiEntire (⟨1, 0⟩ : ℂ)).re = 1 / 2 := by
  rw [re_xi_edge]; ring

/-- R1 at the single point `t = 0`: `0 < Re ξ(1)`, since `Re ξ(1) = 1/2`. -/
theorem R1_at_zero : 0 < (riemannXiEntire (⟨1, 0⟩ : ℂ)).re := by
  rw [re_xi_edge_zero]; norm_num

/-- R3 at the single point `t = 15`: `Re ξ(1+15i) < 0`, from the certified panel
union `top15_re_lt_neg_1e4` at `σ = 1`. -/
theorem R3_at_fifteen : (riemannXiEntire (⟨1, 15⟩ : ℂ)).re < 0 := by
  have h := RiemannXiTopUnion.top15_re_lt_neg_1e4 (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (le_refl (1 : ℝ))
  linarith

/-! ## §2 — The finite-subdivision chaining lemma (route §3/§9)

A finite cover of `Icc a b` by consecutive closed sub-boxes
`a = x₀ ≤ x₁ ≤ … ≤ xₙ = b`, each carrying `∀ t ∈ [xᵢ,xᵢ₊₁], P t`, yields
`∀ t ∈ [a,b], P t`. Packaged as a `List.Chain` over the relation that bundles the
order step with the box property, so the breakpoints and their per-box proofs
travel together. Pure real analysis; no numerics. -/

/-- **Finite-cover chaining.** If `a :: (ms ++ [b])` is a chain under
`fun x y => x ≤ y ∧ ∀ t ∈ [x,y], P t`, then `P` holds on all of `[a,b]`. -/
theorem forall_Icc_cover {P : ℝ → Prop} :
    ∀ (ms : List ℝ) (a b : ℝ),
      List.Chain (fun x y => x ≤ y ∧ ∀ t ∈ Set.Icc x y, P t) a (ms ++ [b]) →
      ∀ t ∈ Set.Icc a b, P t := by
  intro ms
  induction ms with
  | nil =>
      intro a b hch t ht
      rw [List.nil_append] at hch
      cases hch with
      | cons hab _ =>
          obtain ⟨_, h2⟩ := hab
          exact h2 t ht
  | cons m rest ih =>
      intro a b hch t ht
      rw [List.cons_append] at hch
      cases hch with
      | cons ham hrest =>
          obtain ⟨_, hbox⟩ := ham
          rw [Set.mem_Icc] at ht
          rcases le_or_gt t m with hle | hlt
          · exact hbox t (Set.mem_Icc.mpr ⟨ht.1, hle⟩)
          · exact ih m b hrest t (Set.mem_Icc.mpr ⟨le_of_lt hlt, ht.2⟩)

/-! ## §3 — Per-sub-box bridges: enclosure + interval check ⟹ sign

Each lemma takes a certified `EdgeReEnclosure`/`EdgeImEnclosure` over one `t`-box
at `σ = 1` and a single producer-supplied interval inequality (`h_arith`), and
concludes the box sign. `h_arith` quantifies over the enclosure interval and the
`t`-box because the producer only knows `Re Λ₀`, `Im Λ₀` lie in the certified box;
it is the pure-rational obligation a quadrature discharges (e.g. by `nlinarith`).
No such enclosure instance exists at the pin — see the header. -/

/-- **R1 box** — `0 < Re ξ(1+it)` on `[t_lo,t_hi]`. -/
theorem R1_box {t_lo t_hi A1 B1 A2 B2 : ℝ}
    (h_re : EdgeReEnclosure t_lo t_hi 1 A1 B1)
    (h_im : EdgeImEnclosure t_lo t_hi 1 A2 B2)
    (h_arith : ∀ r s t : ℝ, A1 ≤ r → r ≤ B1 → A2 ≤ s → s ≤ B2 →
        t_lo ≤ t → t ≤ t_hi → 0 < (1 - t ^ 2 * r - t * s) / 2) :
    ∀ t ∈ Set.Icc t_lo t_hi, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  intro t ht
  rw [Set.mem_Icc] at ht
  rw [re_xi_edge]
  obtain ⟨hr1, hr2⟩ := h_re.bounds t ht.1 ht.2
  obtain ⟨hs1, hs2⟩ := h_im.bounds t ht.1 ht.2
  exact h_arith _ _ t hr1 hr2 hs1 hs2 ht.1 ht.2

/-- **R2 box** — `0 < Im ξ(1+it)` on `[t_lo,t_hi]`. -/
theorem R2_box {t_lo t_hi A1 B1 A2 B2 : ℝ}
    (h_re : EdgeReEnclosure t_lo t_hi 1 A1 B1)
    (h_im : EdgeImEnclosure t_lo t_hi 1 A2 B2)
    (h_arith : ∀ r s t : ℝ, A1 ≤ r → r ≤ B1 → A2 ≤ s → s ≤ B2 →
        t_lo ≤ t → t ≤ t_hi → 0 < (-t ^ 2 * s + t * r) / 2) :
    ∀ t ∈ Set.Icc t_lo t_hi, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im := by
  intro t ht
  rw [Set.mem_Icc] at ht
  rw [im_xi_edge]
  obtain ⟨hr1, hr2⟩ := h_re.bounds t ht.1 ht.2
  obtain ⟨hs1, hs2⟩ := h_im.bounds t ht.1 ht.2
  exact h_arith _ _ t hr1 hr2 hs1 hs2 ht.1 ht.2

/-- **R3 box** — `Re ξ(1+it) < 0` on `[t_lo,t_hi]`. Derived from `re_xi_edge`
directly (r331c's §4 upper consumer is not in its olean; see the header). -/
theorem R3_box {t_lo t_hi A1 B1 A2 B2 : ℝ}
    (h_re : EdgeReEnclosure t_lo t_hi 1 A1 B1)
    (h_im : EdgeImEnclosure t_lo t_hi 1 A2 B2)
    (h_arith : ∀ r s t : ℝ, A1 ≤ r → r ≤ B1 → A2 ≤ s → s ≤ B2 →
        t_lo ≤ t → t ≤ t_hi → (1 - t ^ 2 * r - t * s) / 2 < 0) :
    ∀ t ∈ Set.Icc t_lo t_hi, (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0 := by
  intro t ht
  rw [Set.mem_Icc] at ht
  rw [re_xi_edge]
  obtain ⟨hr1, hr2⟩ := h_re.bounds t ht.1 ht.2
  obtain ⟨hs1, hs2⟩ := h_im.bounds t ht.1 ht.2
  exact h_arith _ _ t hr1 hr2 hs1 hs2 ht.1 ht.2

/-! ## §4 — Segment assembly: a finite chain of box signs ⟹ R1 / R2 / R3

Each conclusion is syntactically the hypothesis
`rectangleIntegral'_logDeriv_eq_two_of_right_edge` (RightEdgeSigns_2026_10_08)
consumes. Supplying the `List.Chain` requires per-box `EdgeRe/ImEnclosure`
instances, which the absent producer alone can give. -/

/-- R1 from a finite cover of `[0,13]`. -/
theorem R1_of_cover (ms : List ℝ)
    (hch : List.Chain
      (fun x y => x ≤ y ∧ ∀ t ∈ Set.Icc x y, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re)
      0 (ms ++ [13])) :
    ∀ t ∈ Set.Icc (0 : ℝ) 13, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  forall_Icc_cover (P := fun t => 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re) ms 0 13 hch

/-- R2 from a finite cover of `[13,29/2]`. -/
theorem R2_of_cover (ms : List ℝ)
    (hch : List.Chain
      (fun x y => x ≤ y ∧ ∀ t ∈ Set.Icc x y, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im)
      13 (ms ++ [29 / 2])) :
    ∀ t ∈ Set.Icc (13 : ℝ) (29 / 2), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im :=
  forall_Icc_cover (P := fun t => 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im) ms 13 (29 / 2) hch

/-- R3 from a finite cover of `[29/2,15]`. -/
theorem R3_of_cover (ms : List ℝ)
    (hch : List.Chain
      (fun x y => x ≤ y ∧ ∀ t ∈ Set.Icc x y, (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0)
      (29 / 2) (ms ++ [15])) :
    ∀ t ∈ Set.Icc (29 / 2 : ℝ) 15, (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0 :=
  forall_Icc_cover (P := fun t => (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0) ms (29 / 2) 15 hch

end

/-! ## §Axiom check -/

#print axioms re_xi_edge
#print axioms im_xi_edge
#print axioms re_xi_edge_zero
#print axioms R1_at_zero
#print axioms R3_at_fifteen
#print axioms forall_Icc_cover
#print axioms R1_box
#print axioms R2_box
#print axioms R3_box
#print axioms R1_of_cover
#print axioms R2_of_cover
#print axioms R3_of_cover

end RightEdgeSignsProof20261009
end PrincipiaTractalis

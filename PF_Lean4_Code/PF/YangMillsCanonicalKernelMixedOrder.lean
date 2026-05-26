/-
# Yang-Mills Canonical Kernel — Heat-Kernel Sylvester Triple in the
  Wave 26 Mixed-Order Cluster-Fix Family?

## Strategic context (2026-05-25, Wave 27 YM follow-on to Wave 26)

Wave 26 (`YangMillsMixedOrderKernelCalculus`, commit a2679aa) PROVED
that the mixed-order kernel calculus `K_mixed = a·M² + b·M + c·I` on
the level-1 YM cluster matrix `M_cluster` (eigenvalues `{1/2, 3/2}`)
realises the Wave 24 cluster-fix family via Sylvester functional
calculus. The 1-parameter cluster-fix family is:

    b = (c₂ − c₁) − 2·a
    c = (3·c₁ − c₂)/2 + 3·a/4                                  (★)

for any free leading coefficient `a ∈ ℝ` and any target cluster-image
pair `(c₁, c₂) ∈ ℝ²`.

Open question after Wave 26 (this file's target):

  **Does some CANONICAL operator construction produce a Sylvester
  triple `(a, b, c)` lying in the cluster-fix family with NATURAL
  cluster-image targets `(c₁, c₂) ∈ {1/2, 3/2}²`?**

The leading candidate is the **heat-kernel Taylor truncation**:

    e^{−t·M_cluster}  ≈  I − t·M_cluster + (t²/2)·M_cluster²
    =  a·M_cluster² + b·M_cluster + c·I
    with                  (a, b, c) = (t²/2, −t, 1).             (♥)

This is the most natural second-order operator-theoretic construction
in spectral / parabolic PDE / quantum-mechanical contexts. Does it lie
in the Wave 26 cluster-fix family for some t > 0?

## Honest finding (NEGATIVE / NARROW-OUT)

Substituting `(♥)` into `(★)`:

    Eqn 1:  −t = (c₂ − c₁) − t²    ⟹   c₂ − c₁ = t² − t
    Eqn 2:  1 = (3·c₁ − c₂)/2 + 3·t²/8

Solving:

    c₁ = 1 + t²/8 − t/2
    c₂ = c₁ + t² − t  =  1 + 9·t²/8 − 3·t/2

These are the **forced** cluster images induced by the heat-kernel
triple at parameter `t`. Question: for which `t > 0` are BOTH images
in the natural target set `{1/2, 3/2}`?

  * `c₁ = 1/2`:  t² − 4·t + 4 = 0  ⟹  `t = 2`. Then `c₂ = 5/2` ≠ 1/2, 3/2.
  * `c₁ = 3/2`:  t² − 4·t − 4 = 0  ⟹  `t = 2 + 2·√2 ≈ 4.83`. Then `c₂ = …` ≠ targets.
  * `c₂ = 1/2`:  9·t² − 12·t + 4 = 0  ⟹  `t = 2/3` (double root). Then `c₁ = 1 + (4/9)/8 − 1/3 = 13/18` ≠ targets.
  * `c₂ = 3/2`:  9·t² − 12·t − 4 = 0  ⟹  `t = (2 + 2·√2)/3 ≈ 1.61`. Then `c₁ = …` ≠ targets.

Furthermore, the SIMULTANEOUS pairings (1/2, 3/2) and (1/2, 1/2) fail:

  * `(c₁, c₂) = (1/2, 3/2)`:  Eqn 1 gives `t² − t = 1` (so `t = (1+√5)/2 = φ`);
    Eqn 2 gives `3·c₁ − c₂ = 0`, then `2·c₁ = 2 + t²/4 − t = 2 + (t²−t)/4 − 3·t/4`;
    requires `t = 5/3`, but `t² − t = 25/9 − 15/9 = 10/9 ≠ 1`. CONTRADICTION.
  * `(c₁, c₂) = (1/2, 1/2)`:  Eqn 1 gives `t² − t = 0`, so `t ∈ {0, 1}`;
    at `t = 1`, Eqn 2 requires `1 = 1 + 3/8 = 11/8`. CONTRADICTION.
    (`t = 0` is the trivial identity, not a heat flow.)
  * `(c₁, c₂) = (3/2, 3/2)`:  Eqn 1 gives `t² − t = 0`; same `t = 1`.
    Eqn 2 needs `1 = 3 + 3/8`. CONTRADICTION.
  * `(c₁, c₂) = (3/2, 1/2)`:  Eqn 1 gives `t² − t = −1`; no REAL t.

**Conclusion**: NO real `t > 0` makes the heat-kernel Taylor triple
`(t²/2, −t, 1)` realise a Wave 24 natural cluster-fix pairing
`(c₁, c₂) ∈ {1/2, 3/2}²` at the operator level via Sylvester functional
calculus on `M_cluster`.

The heat-kernel route is **NARROWED OUT** as a canonical witness for
the cluster-fix mechanism.

## Strategic verdict (per dispatch outcome 2)

The heat-kernel mixed-order Taylor truncation is the most natural
operator-theoretic candidate for producing the Wave 24 triple, but it
**FAILS** to land in the natural-target cluster-fix family. This
narrows the next open question to other canonical constructions
(resolvent expansion, partial fractions of `1/(M − μ)`, propagator
series, …).

The mixed-order Sylvester calculus is structurally available (Wave 26
positive result) but its canonical operator origin remains open.

## What this file proves (all axiom-free)

  1. `heatKernelTaylorTriple t := (t²/2, −t, 1)`.
  2. `heatKernelInducedMap t λ := (t²/2)·λ² + (−t)·λ + 1`.
  3. The induced map equals Wave 26's `mixedOrderKernelMap` at the
     heat-kernel triple.
  4. CLUSTER-IMAGE FORMULAE:
       • `heatKernelInducedMap t (1/2) = 1 − t/2 + t²/8`
       • `heatKernelInducedMap t (3/2) = 1 − 3·t/2 + 9·t²/8`
  5. DIFFERENCE IDENTITY (inherited from Wave 26):
       • `heatKernelInducedMap t (3/2) − heatKernelInducedMap t (1/2)
          = t² − t`.
  6. The heat-kernel triple lies in the Wave 26 1-parameter
     cluster-fix family with c₁(t) := 1 + t²/8 − t/2,
     c₂(t) := 1 + 9·t²/8 − 3·t/2.
  7. NARROW-OUT THEOREMS: at NO real `t` does the heat-kernel triple
     achieve any of the four `(1/2, 3/2)² ` pairings:
       a. `(1/2, 1/2)` — collapse-low      — FAILS
       b. `(1/2, 3/2)` — pointwise         — FAILS
       c. `(3/2, 1/2)` — cross-cluster     — FAILS (no real t)
       d. `(3/2, 3/2)` — collapse-high     — FAILS
  8. **Capstone** `ym_canonical_heat_kernel_misses_cluster_fix`:
     the canonical heat-kernel Taylor-truncation route to Wave 24
     cluster fixing is NARROWED OUT, while the Wave 26 abstract
     mixed-order realisation remains intact.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

## Honest scope

This file does NOT discharge the YM mass gap. It documents a NEGATIVE
finding: the **most natural** second-order operator-theoretic
construction (heat-kernel Taylor truncation) does NOT produce the
Wave 24 cluster-fix triples. The Wave 26 mixed-order calculus
realisation is structural (Sylvester), not derived from a canonical
operator construction. The open question — "what canonical operator
construction produces the specific Wave 24 triple `(1, −2, 5/4)` or
`(1, −1, 3/4)`?" — is **narrowed**: heat kernel is out, next
candidates are resolvent / partial-fraction / propagator-series
expansions.

Author: Pablo Cohen (with assistance). 2026-05-25 Wave 27 YM follow-on.
-/

import PF.YangMillsMixedOrderKernelCalculus

namespace PrincipiaTractalis

open Real

/-! ## Part 1 — The heat-kernel Taylor triple

The order-2 Taylor truncation of `exp(−t · M)`:

    e^{−t·M}  =  I − t·M + (t²/2)·M² + O(t³·M³)

retains the leading three terms `(t²/2)·M² + (−t)·M + 1·I`, which in
the mixed-order Sylvester form `a·M² + b·M + c·I` corresponds to the
triple `(a, b, c) = (t²/2, −t, 1)`. -/

/-- **Heat-kernel Taylor-truncation triple** (axiom-free).

    The order-2 Taylor coefficients of `e^{−t·M}` interpreted as a
    mixed-order Sylvester triple `(a, b, c)`. -/
noncomputable def heatKernelTaylorTriple (t : ℝ) : ℝ × ℝ × ℝ :=
  (t^2 / 2, -t, 1)

/-- **Heat-kernel induced eigenvalue map** (axiom-free).

    The Sylvester-induced map of the heat-kernel Taylor truncation on
    a 2×2 symmetric matrix with eigenvalues in the cluster. -/
noncomputable def heatKernelInducedMap (t lam : ℝ) : ℝ :=
  mixedOrderKernelMap (t^2 / 2) (-t) 1 lam

/-- **Heat-kernel triple values**: extracts `(a, b, c)` as a triple
    of explicit closed-form expressions (axiom-free). -/
theorem heatKernelTaylorTriple_eq (t : ℝ) :
    heatKernelTaylorTriple t = (t^2 / 2, -t, 1) := rfl

/-- **Heat-kernel induced map agrees with Wave 26 mixed-order map at the
    heat-kernel triple** (axiom-free). -/
theorem heatKernelInducedMap_eq_mixedOrder (t lam : ℝ) :
    heatKernelInducedMap t lam = mixedOrderKernelMap (t^2 / 2) (-t) 1 lam := rfl

/-- **Heat-kernel induced map closed form** (axiom-free):
    `heatKernelInducedMap t λ = (t²/2)·λ² − t·λ + 1`. -/
theorem heatKernelInducedMap_closed_form (t lam : ℝ) :
    heatKernelInducedMap t lam = (t^2 / 2) * lam^2 + (-t) * lam + 1 := by
  unfold heatKernelInducedMap
  rw [mixedOrderKernelMap_eq]

/-! ## Part 2 — Cluster-image formulae at the heat-kernel triple

The forced cluster images at the heat-kernel parameter `t`:

    heatKernelInducedMap t (1/2) = 1 − t/2 + t²/8
    heatKernelInducedMap t (3/2) = 1 − 3·t/2 + 9·t²/8 -/

/-- **Lower cluster centre image** (axiom-free):
    `heatKernelInducedMap t (1/2) = 1 − t/2 + t²/8`. -/
theorem heatKernelInducedMap_at_half (t : ℝ) :
    heatKernelInducedMap t (1/2) = 1 - t/2 + t^2/8 := by
  unfold heatKernelInducedMap
  rw [mixedOrderKernelMap_at_half]
  ring

/-- **Upper cluster centre image** (axiom-free):
    `heatKernelInducedMap t (3/2) = 1 − 3·t/2 + 9·t²/8`. -/
theorem heatKernelInducedMap_at_three_halves (t : ℝ) :
    heatKernelInducedMap t (3/2) = 1 - 3*t/2 + 9*t^2/8 := by
  unfold heatKernelInducedMap
  rw [mixedOrderKernelMap_at_three_halves]
  ring

/-- **Heat-kernel cluster-image difference identity** (axiom-free):

      heatKernelInducedMap t (3/2) − heatKernelInducedMap t (1/2)
        = t² − t.

    This is the Wave 26 `mixedOrderKernelMap_difference` specialised
    to the heat-kernel triple `(t²/2, −t, 1)`: `2·a + b = t² − t`. -/
theorem heatKernelInducedMap_difference (t : ℝ) :
    heatKernelInducedMap t (3/2) - heatKernelInducedMap t (1/2)
      = t^2 - t := by
  rw [heatKernelInducedMap_at_three_halves, heatKernelInducedMap_at_half]
  ring

/-! ## Part 3 — The heat-kernel triple lies in the Wave 26 1-parameter
    cluster-fix family with FORCED target images

Setting `a := t²/2`, the Wave 26 family `(★)` forces:
  c₁(t) := 1 + t²/8 − t/2
  c₂(t) := 1 + 9·t²/8 − 3·t/2

The heat-kernel triple then realises `(K_mixed(1/2), K_mixed(3/2)) =
(c₁(t), c₂(t))` automatically. This is the operator-level statement
"heat kernel lives in the mixed-order family". -/

/-- **Heat-kernel triple realises the Wave 26 family with forced targets**
    (axiom-free).

    For every real `t`, the heat-kernel Taylor truncation lies in the
    Wave 26 1-parameter cluster-fix family at parameters
      • `a = t²/2`
      • `b = −t = (c₂(t) − c₁(t)) − 2·a`
      • `c = 1 = (3·c₁(t) − c₂(t))/2 + 3·a/4`
    with FORCED cluster targets
      • `c₁(t) := 1 + t²/8 − t/2`
      • `c₂(t) := 1 + 9·t²/8 − 3·t/2`. -/
theorem heatKernel_lies_in_mixed_order_family (t : ℝ) :
    heatKernelInducedMap t (1/2) = 1 + t^2/8 - t/2 ∧
    heatKernelInducedMap t (3/2) = 1 + 9*t^2/8 - 3*t/2 := by
  refine ⟨?_, ?_⟩
  · rw [heatKernelInducedMap_at_half]; ring
  · rw [heatKernelInducedMap_at_three_halves]; ring

/-! ## Part 4 — Narrow-out theorems

The natural Wave 24 cluster-fix targets are `(c₁, c₂) ∈ {1/2, 3/2}²`,
four pairings. We show NO real `t` makes the heat-kernel triple hit
any of them. -/

/-- **NARROW-OUT (1/2, 1/2) collapse-low** (axiom-free).

    No real `t` achieves `heatKernelInducedMap t (1/2) = 1/2 ∧
    heatKernelInducedMap t (3/2) = 1/2`. The difference identity
    `t² − t = c₂ − c₁ = 0` forces `t ∈ {0, 1}`; at `t = 1` the lower
    image is `1 − 1/2 + 1/8 = 5/8 ≠ 1/2`; at `t = 0` the map is
    identity which sends `1/2 ↦ 1` ≠ 1/2. -/
theorem heatKernel_misses_collapse_low :
    ¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 1/2 ∧
               heatKernelInducedMap t (3/2) = 1/2 := by
  intro ⟨t, h1, h2⟩
  -- From the difference identity: c₂ − c₁ = 0 ⟹ t² − t = 0 ⟹ t·(t−1) = 0
  have hdiff : t^2 - t = 0 := by
    have := heatKernelInducedMap_difference t
    rw [h1, h2] at this
    linarith
  -- Factor: t · (t − 1) = 0
  have hfac : t * (t - 1) = 0 := by ring_nf; linarith [hdiff]
  rcases mul_eq_zero.mp hfac with ht0 | ht1
  · -- t = 0: heatKernelInducedMap 0 (1/2) = 1 ≠ 1/2
    rw [heatKernelInducedMap_at_half, ht0] at h1
    norm_num at h1
  · -- t = 1: heatKernelInducedMap 1 (1/2) = 5/8 ≠ 1/2
    have ht : t = 1 := by linarith
    rw [heatKernelInducedMap_at_half, ht] at h1
    norm_num at h1

/-- **NARROW-OUT (3/2, 3/2) collapse-high** (axiom-free).

    Same `t² − t = 0` constraint; at `t = 1` the upper image is
    `1 − 3/2 + 9/8 = 5/8 ≠ 3/2`; at `t = 0` it's `1 ≠ 3/2`. -/
theorem heatKernel_misses_collapse_high :
    ¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 3/2 ∧
               heatKernelInducedMap t (3/2) = 3/2 := by
  intro ⟨t, h1, h2⟩
  have hdiff : t^2 - t = 0 := by
    have := heatKernelInducedMap_difference t
    rw [h1, h2] at this
    linarith
  have hfac : t * (t - 1) = 0 := by ring_nf; linarith [hdiff]
  rcases mul_eq_zero.mp hfac with ht0 | ht1
  · rw [heatKernelInducedMap_at_half, ht0] at h1
    norm_num at h1
  · have ht : t = 1 := by linarith
    rw [heatKernelInducedMap_at_half, ht] at h1
    norm_num at h1

/-- **NARROW-OUT (3/2, 1/2) cross-cluster swap** (axiom-free).

    The difference identity forces `t² − t = c₂ − c₁ = −1`, i.e.
    `t² − t + 1 = 0`. Its discriminant `1 − 4 = −3 < 0` has NO real
    solution — the heat-kernel route cannot achieve the cross-cluster
    swap pairing at all. -/
theorem heatKernel_misses_cross_swap :
    ¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 3/2 ∧
               heatKernelInducedMap t (3/2) = 1/2 := by
  intro ⟨t, h1, h2⟩
  have hdiff : t^2 - t = -1 := by
    have := heatKernelInducedMap_difference t
    rw [h1, h2] at this
    linarith
  -- Show t² - t ≥ -1/4 (completing the square: (t − 1/2)² ≥ 0 ⟹ t² − t ≥ -1/4)
  have hsq : (t - 1/2)^2 ≥ 0 := sq_nonneg _
  have : t^2 - t ≥ -1/4 := by nlinarith [hsq]
  linarith

/-- **NARROW-OUT (1/2, 3/2) pointwise fix** (axiom-free).

    The difference identity forces `t² − t = 1`. The lower-image
    equation `1 − t/2 + t²/8 = 1/2` rearranges to `t² − 4·t + 4 = 0`,
    i.e. `(t − 2)² = 0`, so `t = 2`. But then `t² − t = 4 − 2 = 2 ≠ 1`.
    CONTRADICTION. -/
theorem heatKernel_misses_pointwise :
    ¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 1/2 ∧
               heatKernelInducedMap t (3/2) = 3/2 := by
  intro ⟨t, h1, h2⟩
  -- difference forces t² − t = 1
  have hdiff : t^2 - t = 1 := by
    have := heatKernelInducedMap_difference t
    rw [h1, h2] at this
    linarith
  -- lower image forces (t − 2)² = 0
  have hlow : 1 - t/2 + t^2/8 = 1/2 := by
    rw [← heatKernelInducedMap_at_half]; exact h1
  have hsq : (t - 2)^2 = 0 := by nlinarith [hlow]
  have ht : t = 2 := by
    have := sq_eq_zero_iff.mp hsq
    linarith
  -- contradiction with t² − t = 1
  rw [ht] at hdiff
  norm_num at hdiff

/-! ## Part 5 — Strategic capstone: heat-kernel route NARROWED OUT -/

/-- **★★★ Heat-kernel canonical-construction NARROW-OUT — strategic capstone**
    (axiom-free).

    The canonical heat-kernel Taylor-truncation operator construction
    `e^{−t·M_cluster} ≈ I − t·M_cluster + (t²/2)·M_cluster²` with
    Sylvester triple `(a, b, c) = (t²/2, −t, 1)` does NOT realise ANY of
    the four natural cluster-fix pairings `(c₁, c₂) ∈ {1/2, 3/2}²`.

    Specifically:
      (a) Heat-kernel triple lies in the Wave 26 family (structural).
      (b) NO real `t` gives `(c₁, c₂) = (1/2, 1/2)` (collapse-low).
      (c) NO real `t` gives `(c₁, c₂) = (1/2, 3/2)` (pointwise).
      (d) NO real `t` gives `(c₁, c₂) = (3/2, 1/2)` (cross-swap, no real t).
      (e) NO real `t` gives `(c₁, c₂) = (3/2, 3/2)` (collapse-high).

    OUTCOME (Wave 27 narrow-out): the heat-kernel Taylor-truncation
    route to the Wave 24 cluster-fix mechanism is NARROWED OUT. The
    canonical operator-theoretic origin of the specific Wave 24 triple
    `(1, −2, 5/4)` or `(1, −1, 3/4)` must come from a DIFFERENT
    construction (next candidates: resolvent expansion, partial
    fractions of `1/(M − μ)`, propagator series). -/
theorem ym_canonical_heat_kernel_misses_cluster_fix :
    -- (a) Heat-kernel triple structurally lies in the Wave 26 family
    (∀ t : ℝ, heatKernelInducedMap t (1/2) = 1 + t^2/8 - t/2 ∧
              heatKernelInducedMap t (3/2) = 1 + 9*t^2/8 - 3*t/2) ∧
    -- (b) Collapse-low (1/2, 1/2) is unreachable
    (¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 1/2 ∧
                heatKernelInducedMap t (3/2) = 1/2) ∧
    -- (c) Pointwise (1/2, 3/2) is unreachable
    (¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 1/2 ∧
                heatKernelInducedMap t (3/2) = 3/2) ∧
    -- (d) Cross-swap (3/2, 1/2) is unreachable
    (¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 3/2 ∧
                heatKernelInducedMap t (3/2) = 1/2) ∧
    -- (e) Collapse-high (3/2, 3/2) is unreachable
    (¬ ∃ t : ℝ, heatKernelInducedMap t (1/2) = 3/2 ∧
                heatKernelInducedMap t (3/2) = 3/2) :=
  ⟨heatKernel_lies_in_mixed_order_family,
   heatKernel_misses_collapse_low,
   heatKernel_misses_pointwise,
   heatKernel_misses_cross_swap,
   heatKernel_misses_collapse_high⟩

/-! ## Part 6 — Axiom-freeness verification -/

#print axioms heatKernelInducedMap_eq_mixedOrder
#print axioms heatKernelInducedMap_closed_form
#print axioms heatKernelInducedMap_at_half
#print axioms heatKernelInducedMap_at_three_halves
#print axioms heatKernelInducedMap_difference
#print axioms heatKernel_lies_in_mixed_order_family
#print axioms heatKernel_misses_collapse_low
#print axioms heatKernel_misses_collapse_high
#print axioms heatKernel_misses_cross_swap
#print axioms heatKernel_misses_pointwise
#print axioms ym_canonical_heat_kernel_misses_cluster_fix

end PrincipiaTractalis

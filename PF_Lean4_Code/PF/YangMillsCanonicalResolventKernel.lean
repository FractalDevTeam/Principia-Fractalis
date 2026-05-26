/-
# Yang-Mills Canonical Resolvent Kernel — Sylvester Triple in the
  Wave 26 Mixed-Order Cluster-Fix Family?

## Strategic context (2026-05-25, Wave 27 YM follow-on to a666399)

Wave 26 (`YangMillsMixedOrderKernelCalculus`, commit a2679aa) PROVED
that the mixed-order kernel calculus `K_mixed = a·M² + b·M + c·I` on
the level-1 YM cluster matrix `M_cluster` (eigenvalues `{1/2, 3/2}`)
realises the Wave 24 cluster-fix family via Sylvester functional
calculus. The 1-parameter cluster-fix family is:

    b = (c₂ − c₁) − 2·a
    c = (3·c₁ − c₂)/2 + 3·a/4                                  (★)

for any free leading coefficient `a ∈ ℝ` and any target cluster-image
pair `(c₁, c₂) ∈ ℝ²`.

Wave 27 commit a666399 (`YangMillsCanonicalKernelMixedOrder`) PROVED
that the canonical heat-kernel Taylor truncation
`e^{−t·M} ≈ I − t·M + (t²/2)·M²` with Sylvester triple
`(t²/2, −t, 1)` does NOT achieve any of the four natural cluster-fix
pairings `(c₁, c₂) ∈ {1/2, 3/2}²` for any real `t`. Heat kernel
NARROWED OUT.

This file's target (next canonical candidate):

  **Does the RESOLVENT operator `R(μ) := (M − μI)^(−1)` produce a
  Sylvester triple `(a, b, c)` in the cluster-fix family with NATURAL
  cluster-image targets `(c₁, c₂) ∈ {1/2, 3/2}²` for some real μ?**

## Math (axiom-free, Cayley-Hamilton truncation)

The characteristic polynomial of `M_cluster` (eigenvalues 1/2, 3/2) is
`p(λ) = (λ − 1/2)(λ − 3/2) = λ² − 2λ + 3/4`. By Cayley-Hamilton,
`M² = 2·M − (3/4)·I`. For the shifted matrix `N := M − μI` with
characteristic polynomial
`q(λ) = (λ − (1/2−μ))(λ − (3/2−μ)) = λ² − (2−2μ)·λ + D(μ)`
where `D(μ) := (1/2 − μ)(3/2 − μ) = μ² − 2μ + 3/4`, we get

    N² = (2 − 2μ)·N − D(μ)·I

so (when `D(μ) ≠ 0`)

    N^(−1) = (1/D(μ)) · ((2 − 2μ)·I − N)
           = (1/D(μ)) · (−M + (2 − μ)·I).

Hence the RESOLVENT `R(μ) := (M − μI)^(−1)` is a degree-1 polynomial
in `M_cluster` with Sylvester triple

    (a, b, c)  =  (0, −1/D(μ), (2 − μ)/D(μ))                  (♦)

(degree-1 in M, so `a = 0`). The induced eigenvalue map is

    λ ↦ 0·λ² + (−1/D(μ))·λ + (2 − μ)/D(μ)
       = ((2 − μ) − λ) / D(μ).

Sanity checks (axiom-free): at `λ = 1/2`,
`((2 − μ) − 1/2)/D(μ) = (3/2 − μ)/D(μ) = 1/(1/2 − μ)`; at
`λ = 3/2`, `((2 − μ) − 3/2)/D(μ) = (1/2 − μ)/D(μ) = 1/(3/2 − μ)` —
these are the textbook resolvent eigenvalues.

## Honest finding (NEGATIVE / NARROW-OUT)

The resolvent triple `(♦)` automatically lies in the Wave 26 family
`(★)` with `a = 0`:

  • `b = −1/D(μ)` matches `(c₂ − c₁) − 0 = c₂ − c₁` because
    `c₂ − c₁ = 1/(3/2 − μ) − 1/(1/2 − μ) = −1/D(μ)`. ✓
  • `c = (2 − μ)/D(μ)` matches `(3·c₁ − c₂)/2` because
    `(3·c₁ − c₂)/2 = (3/(1/2 − μ) − 1/(3/2 − μ))/2
                   = (3·(3/2 − μ) − (1/2 − μ))/(2·D(μ))
                   = (4 − 2μ)/(2·D(μ)) = (2 − μ)/D(μ)`. ✓

So the structural inclusion in `(★)` is FORCED. The remaining question
is whether the induced cluster images `(c₁, c₂) = (1/(1/2−μ), 1/(3/2−μ))`
can hit any of the four natural target pairings in `{1/2, 3/2}²`.

Solving each cluster image equation:

  • `c₁ = 1/(1/2 − μ) = 1/2`  ⟹  `1/2 − μ = 2`  ⟹  μ = −3/2
  • `c₁ = 1/(1/2 − μ) = 3/2`  ⟹  `1/2 − μ = 2/3`  ⟹  μ = −1/6
  • `c₂ = 1/(3/2 − μ) = 1/2`  ⟹  `3/2 − μ = 2`  ⟹  μ = −1/2
  • `c₂ = 1/(3/2 − μ) = 3/2`  ⟹  `3/2 − μ = 2/3`  ⟹  μ = 5/6

The required μ values are pairwise DIFFERENT — no single μ realises any
pairing:

  • `(c₁, c₂) = (1/2, 1/2)`: needs μ = −3/2 AND μ = −1/2. FAIL.
  • `(c₁, c₂) = (1/2, 3/2)`: needs μ = −3/2 AND μ =  5/6. FAIL.
  • `(c₁, c₂) = (3/2, 1/2)`: needs μ = −1/6 AND μ = −1/2. FAIL.
  • `(c₁, c₂) = (3/2, 3/2)`: needs μ = −1/6 AND μ =  5/6. FAIL.

**Conclusion**: NO real μ (with `D(μ) ≠ 0`, i.e. μ ∉ {1/2, 3/2}) makes
the canonical resolvent triple realise a Wave 24 natural cluster-fix
pairing on `M_cluster`. The resolvent route is **NARROWED OUT** as a
canonical witness for the cluster-fix mechanism.

## Strategic verdict (per dispatch outcome 2)

Two canonical second-order operator-theoretic constructions
(heat-kernel Taylor — Wave 27 a666399; resolvent / Cayley-Hamilton —
THIS FILE) both miss the natural cluster-fix family. The mixed-order
Sylvester calculus is structurally available (Wave 26 positive
result) but its canonical operator origin remains open. Next
candidates: partial fractions of `1/(M − μ)` (a sum of TWO
resolvents at different μ's, giving genuine quadratic-in-M structure
via Cayley-Hamilton expansion), propagator series, Stieltjes
transforms, …

## What this file proves (all axiom-free)

  1. `resolventCayleyHamiltonTriple μ := (0, −1/D(μ), (2 − μ)/D(μ))`
     where `D(μ) := μ² − 2μ + 3/4`.
  2. `resolventInducedMap μ λ := ((2 − μ) − λ) / D(μ)`.
  3. The resolvent induced map agrees with Wave 26's
     `mixedOrderKernelMap` at the resolvent triple (when `D ≠ 0`).
  4. CLUSTER-IMAGE FORMULAE:
       • `resolventInducedMap μ (1/2) = 1/(1/2 − μ)` (when `D ≠ 0`)
       • `resolventInducedMap μ (3/2) = 1/(3/2 − μ)` (when `D ≠ 0`)
  5. The resolvent triple lies in the Wave 26 1-parameter cluster-fix
     family (with `a = 0`) — structural inclusion.
  6. NARROW-OUT THEOREMS: at NO real μ (with `D(μ) ≠ 0`) does the
     resolvent triple achieve any of the four `(1/2, 3/2)² ` pairings:
       a. `(1/2, 1/2)` — collapse-low      — FAILS
       b. `(1/2, 3/2)` — pointwise         — FAILS
       c. `(3/2, 1/2)` — cross-swap        — FAILS
       d. `(3/2, 3/2)` — collapse-high     — FAILS
  7. **Capstone** `ym_canonical_resolvent_misses_cluster_fix`: the
     canonical resolvent (Cayley-Hamilton) route to Wave 24 cluster
     fixing is NARROWED OUT, while the Wave 26 abstract mixed-order
     realisation remains intact.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

## Honest scope

This file does NOT discharge the YM mass gap. It documents a SECOND
NEGATIVE finding (after heat-kernel narrow-out): the canonical
resolvent operator construction does NOT produce the Wave 24
cluster-fix triples on `M_cluster`. Together with Wave 27 a666399
(heat-kernel narrow-out), this leaves the canonical operator origin
of the Wave 26 cluster-fix triples OPEN. Next candidates: partial
fractions, propagator series, dispersion / Stieltjes representations.

Author: Pablo Cohen (with assistance). 2026-05-25 Wave 27 YM follow-on.
-/

import PF.YangMillsMixedOrderKernelCalculus

namespace PrincipiaTractalis

open Real

/-! ## Part 1 — The Cayley-Hamilton determinant `D(μ)`

The characteristic polynomial of `M_cluster − μI` is
`(λ − (1/2 − μ))(λ − (3/2 − μ))`, whose constant term is

    D(μ) := (1/2 − μ)(3/2 − μ) = μ² − 2·μ + 3/4.

This is `det(M_cluster − μI)`. The resolvent is invertible iff
`D(μ) ≠ 0`, i.e. `μ ∉ {1/2, 3/2}`. -/

/-- **Cluster determinant** (axiom-free):
    `D(μ) := (1/2 − μ)(3/2 − μ) = μ² − 2·μ + 3/4`. -/
noncomputable def clusterDet (mu : ℝ) : ℝ := mu^2 - 2*mu + 3/4

/-- **Cluster determinant factored form** (axiom-free). -/
theorem clusterDet_factored (mu : ℝ) :
    clusterDet mu = (1/2 - mu) * (3/2 - mu) := by
  unfold clusterDet; ring

/-- **Cluster determinant value at `μ = 1/2`** (axiom-free):
    `D(1/2) = 0`. -/
theorem clusterDet_at_half : clusterDet (1/2) = 0 := by
  unfold clusterDet; norm_num

/-- **Cluster determinant value at `μ = 3/2`** (axiom-free):
    `D(3/2) = 0`. -/
theorem clusterDet_at_three_halves : clusterDet (3/2) = 0 := by
  unfold clusterDet; norm_num

/-- **Cluster determinant nonzero away from the cluster** (axiom-free).

    For any real `μ` with `μ ≠ 1/2` AND `μ ≠ 3/2`, `D(μ) ≠ 0`. -/
theorem clusterDet_ne_zero_off_cluster (mu : ℝ)
    (h1 : mu ≠ 1/2) (h2 : mu ≠ 3/2) : clusterDet mu ≠ 0 := by
  rw [clusterDet_factored]
  intro hprod
  rcases mul_eq_zero.mp hprod with h | h
  · apply h1; linarith
  · apply h2; linarith

/-! ## Part 2 — The resolvent Cayley-Hamilton triple

By Cayley-Hamilton on `N := M_cluster − μI`:
    N² = (2 − 2μ)·N − D(μ)·I
so for `D(μ) ≠ 0`:
    N^(−1) = (1/D(μ))·((2 − 2μ)·I − N) = (1/D(μ))·(−M + (2 − μ)·I).

This is a DEGREE-1 polynomial in `M`, hence its Sylvester triple has
`a = 0`. -/

/-- **Resolvent Cayley-Hamilton Sylvester triple** (axiom-free).

    For `μ` with `D(μ) ≠ 0`, the resolvent `R(μ) = (M − μI)^(−1)`
    has the Sylvester triple
      `(a, b, c) = (0, −1/D(μ), (2 − μ)/D(μ))`. -/
noncomputable def resolventCayleyHamiltonTriple (mu : ℝ) : ℝ × ℝ × ℝ :=
  (0, -1 / clusterDet mu, (2 - mu) / clusterDet mu)

/-- **Resolvent induced eigenvalue map** (axiom-free).

    The Sylvester-induced map of the resolvent on a 2×2 symmetric
    matrix with eigenvalues in the cluster:
      `R(μ)(λ) = ((2 − μ) − λ) / D(μ)`. -/
noncomputable def resolventInducedMap (mu lam : ℝ) : ℝ :=
  mixedOrderKernelMap 0 (-1 / clusterDet mu) ((2 - mu) / clusterDet mu) lam

/-- **Resolvent induced map agrees with Wave 26 mixed-order map at the
    resolvent triple** (axiom-free; definitional). -/
theorem resolventInducedMap_eq_mixedOrder (mu lam : ℝ) :
    resolventInducedMap mu lam =
      mixedOrderKernelMap 0 (-1 / clusterDet mu)
        ((2 - mu) / clusterDet mu) lam := rfl

/-- **Resolvent induced map closed form** (axiom-free):
    `R(μ)(λ) = ((2 − μ) − λ) / D(μ)`. -/
theorem resolventInducedMap_closed_form (mu lam : ℝ) :
    resolventInducedMap mu lam =
      (-lam + (2 - mu)) / clusterDet mu := by
  unfold resolventInducedMap
  rw [mixedOrderKernelMap_eq]
  rw [neg_div, sub_div]
  ring

/-! ## Part 3 — Cluster-image formulae at the resolvent triple

The resolvent's induced cluster images are the textbook resolvent
eigenvalues:
    R(μ)(1/2) = 1/(1/2 − μ)
    R(μ)(3/2) = 1/(3/2 − μ).

Equivalently `(3/2 − μ)/D(μ) = 1/(1/2 − μ)` (when `D ≠ 0`). -/

/-- **Lower cluster centre image — raw form** (axiom-free):
    `R(μ)(1/2) = ((2 − μ) − 1/2) / D(μ) = (3/2 − μ) / D(μ)`. -/
theorem resolventInducedMap_at_half_raw (mu : ℝ) :
    resolventInducedMap mu (1/2) = (3/2 - mu) / clusterDet mu := by
  rw [resolventInducedMap_closed_form]
  congr 1
  ring

/-- **Upper cluster centre image — raw form** (axiom-free):
    `R(μ)(3/2) = ((2 − μ) − 3/2) / D(μ) = (1/2 − μ) / D(μ)`. -/
theorem resolventInducedMap_at_three_halves_raw (mu : ℝ) :
    resolventInducedMap mu (3/2) = (1/2 - mu) / clusterDet mu := by
  rw [resolventInducedMap_closed_form]
  congr 1
  ring

/-- **Lower cluster image is the textbook resolvent eigenvalue**
    (axiom-free): for `μ ≠ 1/2 ∧ μ ≠ 3/2`,
    `R(μ)(1/2) = 1/(1/2 − μ)`. -/
theorem resolventInducedMap_at_half_eq_inv (mu : ℝ)
    (h1 : mu ≠ 1/2) (h2 : mu ≠ 3/2) :
    resolventInducedMap mu (1/2) = 1 / (1/2 - mu) := by
  rw [resolventInducedMap_at_half_raw, clusterDet_factored]
  have h32 : (3/2 - mu) ≠ 0 := by intro h; apply h2; linarith
  have h12 : (1/2 - mu) ≠ 0 := by intro h; apply h1; linarith
  -- (3/2 − μ) / ((1/2 − μ)·(3/2 − μ)) = 1 / (1/2 − μ)
  rw [mul_comm (1/2 - mu) (3/2 - mu), ← div_div, div_self h32]

/-- **Upper cluster image is the textbook resolvent eigenvalue**
    (axiom-free): for `μ ≠ 1/2 ∧ μ ≠ 3/2`,
    `R(μ)(3/2) = 1/(3/2 − μ)`. -/
theorem resolventInducedMap_at_three_halves_eq_inv (mu : ℝ)
    (h1 : mu ≠ 1/2) (h2 : mu ≠ 3/2) :
    resolventInducedMap mu (3/2) = 1 / (3/2 - mu) := by
  rw [resolventInducedMap_at_three_halves_raw, clusterDet_factored]
  have h32 : (3/2 - mu) ≠ 0 := by intro h; apply h2; linarith
  have h12 : (1/2 - mu) ≠ 0 := by intro h; apply h1; linarith
  -- (1/2 − μ) / ((1/2 − μ)·(3/2 − μ)) = 1 / (3/2 − μ)
  rw [← div_div, div_self h12]

/-! ## Part 4 — The resolvent triple lies in the Wave 26 family
    (structural inclusion with `a = 0`)

The Wave 26 family `(★)` at `a = 0` reduces to
  b = c₂ − c₁,  c = (3·c₁ − c₂)/2.

The resolvent at parameter μ produces FORCED cluster images
  c₁(μ) := R(μ)(1/2) = (3/2 − μ)/D(μ),
  c₂(μ) := R(μ)(3/2) = (1/2 − μ)/D(μ).

We certify the structural inclusion: at these `c₁, c₂` and `a = 0`,
the family parameters `b, c` come out to the resolvent triple values
`(−1/D(μ), (2 − μ)/D(μ))`. -/

/-- **Resolvent triple realises the Wave 26 family with forced targets**
    (axiom-free).

    For every real `μ`, the resolvent Cayley-Hamilton triple lies
    structurally in the Wave 26 family at parameters
      • `a = 0`
      • `b = −1/D(μ)`
      • `c = (2 − μ)/D(μ)`
    with FORCED cluster targets
      • `c₁(μ) := (3/2 − μ)/D(μ)`
      • `c₂(μ) := (1/2 − μ)/D(μ)`. -/
theorem resolvent_lies_in_mixed_order_family (mu : ℝ) :
    resolventInducedMap mu (1/2) = (3/2 - mu) / clusterDet mu ∧
    resolventInducedMap mu (3/2) = (1/2 - mu) / clusterDet mu :=
  ⟨resolventInducedMap_at_half_raw mu, resolventInducedMap_at_three_halves_raw mu⟩

/-! ## Part 5 — Per-image μ uniqueness lemmas

For each target image `(c, value) ∈ {1/2, 3/2} × {1/2, 3/2}`, there is
at most ONE μ achieving it. We pin down the unique μ in each case. -/

/-- **Lower image = 1/2 forces μ = −3/2** (axiom-free).

    If `μ ≠ 1/2 ∧ μ ≠ 3/2` and `R(μ)(1/2) = 1/2`, then `μ = −3/2`. -/
theorem resolvent_lower_eq_half_forces_mu_neg_three_halves (mu : ℝ)
    (h1 : mu ≠ 1/2) (h2 : mu ≠ 3/2)
    (hval : resolventInducedMap mu (1/2) = 1/2) :
    mu = -3/2 := by
  rw [resolventInducedMap_at_half_eq_inv mu h1 h2] at hval
  -- 1/(1/2 − μ) = 1/2  ⟹  1/2 − μ = 2  ⟹  μ = −3/2
  have h12 : (1/2 - mu) ≠ 0 := by intro h; apply h1; linarith
  -- Clear denominators: 1 = (1/2)·(1/2 − μ) ⟹ 1 = 1/4 − μ/2 ⟹ μ = −3/2
  have heq : (1 : ℝ) = (1/2) * (1/2 - mu) := by
    have hd := (div_eq_iff h12).mp hval
    linarith
  linarith

/-- **Lower image = 3/2 forces μ = −1/6** (axiom-free). -/
theorem resolvent_lower_eq_three_halves_forces_mu_neg_one_sixth (mu : ℝ)
    (h1 : mu ≠ 1/2) (h2 : mu ≠ 3/2)
    (hval : resolventInducedMap mu (1/2) = 3/2) :
    mu = -1/6 := by
  rw [resolventInducedMap_at_half_eq_inv mu h1 h2] at hval
  have h12 : (1/2 - mu) ≠ 0 := by intro h; apply h1; linarith
  have heq : (1 : ℝ) = (3/2) * (1/2 - mu) := by
    have hd := (div_eq_iff h12).mp hval
    linarith
  linarith

/-- **Upper image = 1/2 forces μ = −1/2** (axiom-free). -/
theorem resolvent_upper_eq_half_forces_mu_neg_half (mu : ℝ)
    (h1 : mu ≠ 1/2) (h2 : mu ≠ 3/2)
    (hval : resolventInducedMap mu (3/2) = 1/2) :
    mu = -1/2 := by
  rw [resolventInducedMap_at_three_halves_eq_inv mu h1 h2] at hval
  have h32 : (3/2 - mu) ≠ 0 := by intro h; apply h2; linarith
  have heq : (1 : ℝ) = (1/2) * (3/2 - mu) := by
    have hd := (div_eq_iff h32).mp hval
    linarith
  linarith

/-- **Upper image = 3/2 forces μ = 5/6** (axiom-free). -/
theorem resolvent_upper_eq_three_halves_forces_mu_five_sixths (mu : ℝ)
    (h1 : mu ≠ 1/2) (h2 : mu ≠ 3/2)
    (hval : resolventInducedMap mu (3/2) = 3/2) :
    mu = 5/6 := by
  rw [resolventInducedMap_at_three_halves_eq_inv mu h1 h2] at hval
  have h32 : (3/2 - mu) ≠ 0 := by intro h; apply h2; linarith
  have heq : (1 : ℝ) = (3/2) * (3/2 - mu) := by
    have hd := (div_eq_iff h32).mp hval
    linarith
  linarith

/-! ## Part 6 — Narrow-out theorems

The natural Wave 24 cluster-fix targets are `(c₁, c₂) ∈ {1/2, 3/2}²`,
four pairings. We show NO real μ (with `D(μ) ≠ 0`) makes the
resolvent triple hit any of them — each pairing requires TWO
contradictory values of μ. -/

/-- **NARROW-OUT (1/2, 1/2) collapse-low** (axiom-free).

    Lower image = 1/2 forces μ = −3/2; upper image = 1/2 forces
    μ = −1/2; these contradict. -/
theorem resolvent_misses_collapse_low :
    ¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                resolventInducedMap mu (1/2) = 1/2 ∧
                resolventInducedMap mu (3/2) = 1/2 := by
  intro ⟨mu, h1, h2, hlow, hup⟩
  have hA : mu = -3/2 :=
    resolvent_lower_eq_half_forces_mu_neg_three_halves mu h1 h2 hlow
  have hB : mu = -1/2 :=
    resolvent_upper_eq_half_forces_mu_neg_half mu h1 h2 hup
  rw [hA] at hB; norm_num at hB

/-- **NARROW-OUT (1/2, 3/2) pointwise fix** (axiom-free).

    Lower image = 1/2 forces μ = −3/2; upper image = 3/2 forces
    μ = 5/6; these contradict. -/
theorem resolvent_misses_pointwise :
    ¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                resolventInducedMap mu (1/2) = 1/2 ∧
                resolventInducedMap mu (3/2) = 3/2 := by
  intro ⟨mu, h1, h2, hlow, hup⟩
  have hA : mu = -3/2 :=
    resolvent_lower_eq_half_forces_mu_neg_three_halves mu h1 h2 hlow
  have hB : mu = 5/6 :=
    resolvent_upper_eq_three_halves_forces_mu_five_sixths mu h1 h2 hup
  rw [hA] at hB; norm_num at hB

/-- **NARROW-OUT (3/2, 1/2) cross-cluster swap** (axiom-free).

    Lower image = 3/2 forces μ = −1/6; upper image = 1/2 forces
    μ = −1/2; these contradict. -/
theorem resolvent_misses_cross_swap :
    ¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                resolventInducedMap mu (1/2) = 3/2 ∧
                resolventInducedMap mu (3/2) = 1/2 := by
  intro ⟨mu, h1, h2, hlow, hup⟩
  have hA : mu = -1/6 :=
    resolvent_lower_eq_three_halves_forces_mu_neg_one_sixth mu h1 h2 hlow
  have hB : mu = -1/2 :=
    resolvent_upper_eq_half_forces_mu_neg_half mu h1 h2 hup
  rw [hA] at hB; norm_num at hB

/-- **NARROW-OUT (3/2, 3/2) collapse-high** (axiom-free).

    Lower image = 3/2 forces μ = −1/6; upper image = 3/2 forces
    μ = 5/6; these contradict. -/
theorem resolvent_misses_collapse_high :
    ¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                resolventInducedMap mu (1/2) = 3/2 ∧
                resolventInducedMap mu (3/2) = 3/2 := by
  intro ⟨mu, h1, h2, hlow, hup⟩
  have hA : mu = -1/6 :=
    resolvent_lower_eq_three_halves_forces_mu_neg_one_sixth mu h1 h2 hlow
  have hB : mu = 5/6 :=
    resolvent_upper_eq_three_halves_forces_mu_five_sixths mu h1 h2 hup
  rw [hA] at hB; norm_num at hB

/-! ## Part 7 — Strategic capstone: resolvent route NARROWED OUT -/

/-- **★★★ Resolvent canonical-construction NARROW-OUT — strategic capstone**
    (axiom-free).

    The canonical resolvent (Cayley-Hamilton) operator construction
    `R(μ) = (M_cluster − μI)^(−1) = (1/D(μ))·(−M + (2 − μ)·I)` with
    Sylvester triple `(a, b, c) = (0, −1/D(μ), (2 − μ)/D(μ))` does NOT
    realise ANY of the four natural cluster-fix pairings
    `(c₁, c₂) ∈ {1/2, 3/2}²` for any real μ with `D(μ) ≠ 0`.

    Specifically:
      (a) Resolvent triple lies in the Wave 26 family (structural,
          with `a = 0` and forced targets `(3/2−μ)/D(μ), (1/2−μ)/D(μ)`).
      (b) NO real μ gives `(c₁, c₂) = (1/2, 1/2)` (collapse-low).
      (c) NO real μ gives `(c₁, c₂) = (1/2, 3/2)` (pointwise).
      (d) NO real μ gives `(c₁, c₂) = (3/2, 1/2)` (cross-swap).
      (e) NO real μ gives `(c₁, c₂) = (3/2, 3/2)` (collapse-high).

    OUTCOME (Wave 27 narrow-out, second canonical route after
    heat-kernel a666399): the resolvent Cayley-Hamilton route to the
    Wave 24 cluster-fix mechanism is NARROWED OUT. Combined with the
    heat-kernel narrow-out, the canonical operator-theoretic origin of
    the Wave 26 cluster-fix triples remains open. Next candidates:
    PARTIAL FRACTIONS (sum of two resolvents — quadratic in M via
    Cayley-Hamilton expansion), PROPAGATOR SERIES, dispersion /
    Stieltjes representations. -/
theorem ym_canonical_resolvent_misses_cluster_fix :
    -- (a) Resolvent triple structurally lies in the Wave 26 family
    (∀ mu : ℝ,
        resolventInducedMap mu (1/2) = (3/2 - mu) / clusterDet mu ∧
        resolventInducedMap mu (3/2) = (1/2 - mu) / clusterDet mu) ∧
    -- (b) Collapse-low (1/2, 1/2) is unreachable
    (¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                 resolventInducedMap mu (1/2) = 1/2 ∧
                 resolventInducedMap mu (3/2) = 1/2) ∧
    -- (c) Pointwise (1/2, 3/2) is unreachable
    (¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                 resolventInducedMap mu (1/2) = 1/2 ∧
                 resolventInducedMap mu (3/2) = 3/2) ∧
    -- (d) Cross-swap (3/2, 1/2) is unreachable
    (¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                 resolventInducedMap mu (1/2) = 3/2 ∧
                 resolventInducedMap mu (3/2) = 1/2) ∧
    -- (e) Collapse-high (3/2, 3/2) is unreachable
    (¬ ∃ mu : ℝ, mu ≠ 1/2 ∧ mu ≠ 3/2 ∧
                 resolventInducedMap mu (1/2) = 3/2 ∧
                 resolventInducedMap mu (3/2) = 3/2) :=
  ⟨resolvent_lies_in_mixed_order_family,
   resolvent_misses_collapse_low,
   resolvent_misses_pointwise,
   resolvent_misses_cross_swap,
   resolvent_misses_collapse_high⟩

/-! ## Part 8 — Axiom-freeness verification -/

#print axioms clusterDet_factored
#print axioms clusterDet_at_half
#print axioms clusterDet_at_three_halves
#print axioms clusterDet_ne_zero_off_cluster
#print axioms resolventInducedMap_eq_mixedOrder
#print axioms resolventInducedMap_closed_form
#print axioms resolventInducedMap_at_half_raw
#print axioms resolventInducedMap_at_three_halves_raw
#print axioms resolventInducedMap_at_half_eq_inv
#print axioms resolventInducedMap_at_three_halves_eq_inv
#print axioms resolvent_lies_in_mixed_order_family
#print axioms resolvent_lower_eq_half_forces_mu_neg_three_halves
#print axioms resolvent_lower_eq_three_halves_forces_mu_neg_one_sixth
#print axioms resolvent_upper_eq_half_forces_mu_neg_half
#print axioms resolvent_upper_eq_three_halves_forces_mu_five_sixths
#print axioms resolvent_misses_collapse_low
#print axioms resolvent_misses_pointwise
#print axioms resolvent_misses_cross_swap
#print axioms resolvent_misses_collapse_high
#print axioms ym_canonical_resolvent_misses_cluster_fix

end PrincipiaTractalis

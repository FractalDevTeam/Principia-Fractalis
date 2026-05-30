/-
# Yang-Mills Canonical Kernel — Operator-Convex / Midpoint-Convex
  OFF-CLUSTER constraint at the cluster midpoint `λ = 1`.

## Strategic context (2026-05-30, Wave 32 YM follow-on)

Wave 31 (`YangMillsCanonicalOperatorMonotoneKernel.lean`) explored
operator-MONOTONICITY (the Loewner / Nevanlinna–Herglotz structural
axis) and produced the FIRST partial-elimination of a Wave 24
cluster pairing: the cross-swap `(3/2, 1/2)` was STRUCTURALLY
REFUTED by the basic Loewner property (every operator-monotone
function on a real interval is monotone non-decreasing).

This file probes a STRUCTURALLY DIFFERENT axis — operator-CONVEXITY
(the Hansen–Pedersen / Loewner–Heinz structural family) — and finds
a genuinely NEW KIND of constraint: rather than refuting a cluster
pairing, convexity supplies an OFF-CLUSTER UPPER BOUND on `f` at the
cluster spectral midpoint `λ = 1`.

## Mathematical background — midpoint convexity

A function `f : ℝ → ℝ` is **midpoint-convex** iff

    f( (x + y) / 2 )  ≤  ( f(x) + f(y) ) / 2                              (♣)

for all `x, y ∈ ℝ`. This is a STRICTLY WEAKER condition than full
convexity (in the absence of measurability or continuity hypotheses,
Sierpiński / Banach), but it is the canonical AVERAGING constraint
on triples of points and it propagates directly to OPERATOR-CONVEX
functions: every operator-convex function satisfies `f((A+B)/2) ≼
(f(A) + f(B))/2` in the Loewner ordering, which restricted to
SCALAR (1×1) operators reduces to midpoint convexity (♣).

## The cluster spectral midpoint

The Wave 24 YM cluster operator `M_cluster` has spectrum `{1/2, 3/2}`,
with arithmetic mean

    ( 1/2  +  3/2 ) / 2  =  1.

The value `λ = 1` is NOT in the spectrum of `M_cluster`; it sits in
the SPECTRAL GAP between the two cluster eigenvalues. Nevertheless,
for any function `f : ℝ → ℝ` defined on a neighbourhood of `{1/2,
1, 3/2}`, the value `f(1)` is OBSERVABLE as the value of `f` at the
cluster spectral midpoint.

Applying (♣) with `x = 1/2`, `y = 3/2` yields the OFF-CLUSTER bound

    f(1)  ≤  ( f(1/2) + f(3/2) ) / 2                                     (♦)

This is the FILE'S HEADLINE STRUCTURAL FINDING: for every midpoint-
convex `f`, the cluster spectral midpoint value `f(1)` is bounded
above by the arithmetic mean of the cluster IMAGES `f(1/2)` and
`f(3/2)`.

## The four Wave 24 cluster pairings — off-cluster bounds at `λ = 1`

Plugging the four canonical pairings `(c₁, c₂) ∈ {1/2, 3/2}²` into
(♦):

  ┌──────────────────────────┬───────────────────┬──────────────┐
  │ pairing                  │ (c₁ + c₂) / 2     │ f(1) ≤ ?     │
  ├──────────────────────────┼───────────────────┼──────────────┤
  │ pointwise   (1/2, 3/2)   │        1          │ f(1) ≤ 1     │
  │ cross-swap  (3/2, 1/2)   │        1          │ f(1) ≤ 1     │
  │ collapse-lo (1/2, 1/2)   │       1/2         │ f(1) ≤ 1/2   │
  │ collapse-hi (3/2, 3/2)   │       3/2         │ f(1) ≤ 3/2   │
  └──────────────────────────┴───────────────────┴──────────────┘

These are NOT refutations of any pairing — they are UPPER BOUNDS on
the off-cluster value `f(1)`, which any midpoint-convex `f` MUST
satisfy regardless of which pairing it realises. This is a
genuinely NEW kind of structural finding in the Wave 26+ taxonomy:
an OFF-CLUSTER CONSTRAINT, complementing the Wave 26-30 ON-CLUSTER
realisations and the Wave 31 ON-CLUSTER refutation.

## Honest scope

* (♦) is an UPPER BOUND on `f(1)`, not a determination. The same
  cluster pairing can be realised by many functions with different
  `f(1)` values, all satisfying the bound.
* (♣) is the SCALAR consequence of operator-convexity. The full
  operator-convex characterisation (Hansen–Pedersen 1982) involves
  a Stieltjes representation `f(x) = α + β·x + ∫ x²/(t + x) dν(t)`
  and is heavier to formalise; we use only the scalar midpoint
  consequence here, which is sufficient for the off-cluster bound.
* No claim is made that operator-convexity REFUTES any cluster
  pairing. The verdict is OFF-CLUSTER CONSTRAINT, not REFUTATION.

## Positive witness

The IDENTITY `f(x) = x` is midpoint-convex (trivially convex,
in fact affine) and realises the POINTWISE pairing
`(c₁, c₂) = (1/2, 3/2)`. It satisfies the bound `f(1) = 1 ≤ 1`
with equality (the affine case saturates the midpoint inequality).

## What this file proves (all axiom-free)

  1. `MidpointConvex` local definition.
  2. The cluster-midpoint lemma:
     `midpoint_convex_cluster_midpoint_bound` —
     `f(1) ≤ (f(1/2) + f(3/2)) / 2` for any midpoint-convex `f`.
  3. Four pairing-specific off-cluster bounds at `λ = 1`
     (one per Wave 24 cluster pairing).
  4. Positive witness: the identity `f(x) = x` is midpoint-convex
     and realises the pointwise pairing, saturating `f(1) = 1`.
  5. The four bounds combined into a single capstone
     `ym_canonical_convex_imposes_off_cluster_bounds_at_one`.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

Author: Pablo Cohen (with assistance). 2026-05-30 Wave 32 YM
follow-on (operator-convex / Hansen–Pedersen counterpart to
Wave 31 operator-monotone / Loewner).
-/

import Mathlib.Tactic

namespace PrincipiaTractalis

/-! ## Part 1 — Local definition of midpoint convexity

We work with a LOCAL definition rather than depending on mathlib's
`MidpointConvex` (which may not exist or may live behind
heavier imports). The definition is the canonical one:

    f((x + y)/2)  ≤  (f x + f y) / 2

for all `x, y : ℝ`. This is the SCALAR consequence of operator-
convexity on 1×1 matrices, and the basic AVERAGING constraint on
midpoints of arguments and values. -/

/-- **Midpoint convex** (local definition, axiom-free).

    `f : ℝ → ℝ` is midpoint-convex iff for all `x, y : ℝ`,
    `f((x + y)/2) ≤ (f x + f y) / 2`.

    Every convex function (in the standard sense) is midpoint-
    convex; every operator-convex function on a real interval has
    midpoint-convex scalar restriction; midpoint-convex measurable
    functions are convex (Sierpiński / Bernstein–Doetsch). -/
def MidpointConvex (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, f ((x + y) / 2) ≤ (f x + f y) / 2

/-! ## Part 2 — The headline cluster-midpoint lemma.

For any midpoint-convex `f`, the value at the cluster spectral
midpoint `λ = 1 = (1/2 + 3/2)/2` is bounded above by the
arithmetic mean of the cluster images `f(1/2)` and `f(3/2)`.

This is direct from the definition of midpoint convexity applied
to `x = 1/2`, `y = 3/2`; the only arithmetic content is
`(1/2 + 3/2)/2 = 1`. -/

/-- **Cluster spectral midpoint identity** (axiom-free):
    `(1/2 + 3/2)/2 = 1`. -/
theorem cluster_arithmetic_midpoint :
    ((1/2 : ℝ) + 3/2) / 2 = 1 := by norm_num

/-- **Cluster-midpoint upper bound for midpoint-convex `f`**
    (axiom-free).

    For any midpoint-convex `f : ℝ → ℝ`, the value at the cluster
    spectral midpoint `λ = 1` is bounded above by the arithmetic
    mean of the cluster images `f(1/2)` and `f(3/2)`. -/
theorem midpoint_convex_cluster_midpoint_bound
    (f : ℝ → ℝ) (hf : MidpointConvex f) :
    f 1 ≤ (f (1/2) + f (3/2)) / 2 := by
  have h := hf (1/2) (3/2)
  -- h : f ((1/2 + 3/2)/2) ≤ (f (1/2) + f (3/2)) / 2
  have heq : ((1/2 : ℝ) + 3/2) / 2 = 1 := by norm_num
  rw [heq] at h
  exact h

/-! ## Part 3 — Pairing-specific off-cluster bounds at `λ = 1`.

We instantiate the cluster-midpoint bound at each of the four
Wave 24 cluster pairings. Given a midpoint-convex `f` realising
the pairing, the bound becomes a CONCRETE numerical upper bound
on `f(1)`. -/

/-- **Pointwise pairing `(1/2, 3/2)` off-cluster bound at `λ = 1`**
    (axiom-free).

    If `f` is midpoint-convex and realises the pointwise pairing
    `f(1/2) = 1/2 ∧ f(3/2) = 3/2`, then `f(1) ≤ 1`. -/
theorem midpoint_convex_pointwise_off_cluster_bound
    (f : ℝ → ℝ) (hf : MidpointConvex f)
    (h1 : f (1/2) = 1/2) (h2 : f (3/2) = 3/2) :
    f 1 ≤ 1 := by
  have hbnd := midpoint_convex_cluster_midpoint_bound f hf
  rw [h1, h2] at hbnd
  linarith

/-- **Cross-swap pairing `(3/2, 1/2)` off-cluster bound at `λ = 1`**
    (axiom-free).

    If `f` is midpoint-convex and realises the cross-swap pairing
    `f(1/2) = 3/2 ∧ f(3/2) = 1/2`, then `f(1) ≤ 1`. (Same arithmetic
    mean as the pointwise pairing — the spectral midpoint is the
    same.) -/
theorem midpoint_convex_cross_swap_off_cluster_bound
    (f : ℝ → ℝ) (hf : MidpointConvex f)
    (h1 : f (1/2) = 3/2) (h2 : f (3/2) = 1/2) :
    f 1 ≤ 1 := by
  have hbnd := midpoint_convex_cluster_midpoint_bound f hf
  rw [h1, h2] at hbnd
  linarith

/-- **Collapse-low pairing `(1/2, 1/2)` off-cluster bound at `λ = 1`**
    (axiom-free).

    If `f` is midpoint-convex and realises the collapse-low pairing
    `f(1/2) = 1/2 ∧ f(3/2) = 1/2`, then `f(1) ≤ 1/2`. (Stricter
    bound — the cluster images collapse to the lower eigenvalue,
    so the arithmetic mean is `1/2`.) -/
theorem midpoint_convex_collapse_low_off_cluster_bound
    (f : ℝ → ℝ) (hf : MidpointConvex f)
    (h1 : f (1/2) = 1/2) (h2 : f (3/2) = 1/2) :
    f 1 ≤ 1/2 := by
  have hbnd := midpoint_convex_cluster_midpoint_bound f hf
  rw [h1, h2] at hbnd
  linarith

/-- **Collapse-high pairing `(3/2, 3/2)` off-cluster bound at `λ = 1`**
    (axiom-free).

    If `f` is midpoint-convex and realises the collapse-high pairing
    `f(1/2) = 3/2 ∧ f(3/2) = 3/2`, then `f(1) ≤ 3/2`. -/
theorem midpoint_convex_collapse_high_off_cluster_bound
    (f : ℝ → ℝ) (hf : MidpointConvex f)
    (h1 : f (1/2) = 3/2) (h2 : f (3/2) = 3/2) :
    f 1 ≤ 3/2 := by
  have hbnd := midpoint_convex_cluster_midpoint_bound f hf
  rw [h1, h2] at hbnd
  linarith

/-! ## Part 4 — Positive witness: the identity `f(x) = x`.

The identity map `f(x) = x` is midpoint-convex (in fact affine,
hence convex with equality in (♣)). It realises the POINTWISE
pairing `(1/2, 3/2)` and saturates the off-cluster bound with
`f(1) = 1`.

Note: the identity is the SAME positive witness that Wave 31's
operator-monotone analysis used for the pointwise pairing. Here we
verify it ALSO satisfies the midpoint-convexity constraint, with
equality in the cluster-midpoint bound — affine maps saturate every
midpoint inequality. -/

/-- **The identity is midpoint-convex** (axiom-free).

    `idMap x := x` satisfies `idMap((x+y)/2) = (x+y)/2 =
    (idMap x + idMap y)/2`, with EQUALITY (affine maps saturate
    midpoint inequalities). -/
def idMap (x : ℝ) : ℝ := x

theorem idMap_midpoint_convex : MidpointConvex idMap := by
  intro x y
  unfold idMap
  -- Goal: (x + y) / 2 ≤ (x + y) / 2
  linarith

/-- **Identity realises the pointwise cluster pairing — lower
    image** (axiom-free): `idMap(1/2) = 1/2`. -/
theorem idMap_at_half : idMap (1/2) = 1/2 := rfl

/-- **Identity realises the pointwise cluster pairing — upper
    image** (axiom-free): `idMap(3/2) = 3/2`. -/
theorem idMap_at_three_halves : idMap (3/2) = 3/2 := rfl

/-- **Identity at the cluster spectral midpoint** (axiom-free):
    `idMap(1) = 1`. -/
theorem idMap_at_one : idMap 1 = 1 := rfl

/-- **Identity saturates the pointwise off-cluster bound at `λ = 1`**
    (axiom-free).

    The identity `f(x) = x` is midpoint-convex, realises the
    pointwise pairing `f(1/2) = 1/2 ∧ f(3/2) = 3/2`, and saturates
    the off-cluster bound: `f(1) = 1 ≤ 1`. -/
theorem idMap_saturates_pointwise_off_cluster_bound :
    idMap 1 ≤ 1 :=
  midpoint_convex_pointwise_off_cluster_bound
    idMap idMap_midpoint_convex idMap_at_half idMap_at_three_halves

/-! ## Part 5 — Joint positive witness packaging.

We package the identity-as-witness facts as a single conjunction
for the capstone. -/

/-- **JOINT POSITIVE WITNESS — identity realises pointwise pairing
    and saturates the off-cluster bound** (axiom-free). -/
theorem idMap_realises_pointwise_and_saturates_bound :
    MidpointConvex idMap ∧
    idMap (1/2) = 1/2 ∧
    idMap (3/2) = 3/2 ∧
    idMap 1 = 1 ∧
    idMap 1 ≤ 1 :=
  ⟨idMap_midpoint_convex,
   idMap_at_half,
   idMap_at_three_halves,
   idMap_at_one,
   idMap_saturates_pointwise_off_cluster_bound⟩

/-! ## Part 6 — Strategic capstone: OFF-CLUSTER constraint.

The operator-convex / midpoint-convex canonical functional form
yields a genuinely NEW KIND of structural finding in the Wave 26+
taxonomy:

  ┌──────────────────────────┬──────────────────────────────────┐
  │ pairing                  │ midpoint-convex off-cluster bound│
  ├──────────────────────────┼──────────────────────────────────┤
  │ pointwise   (1/2, 3/2)   │ f(1) ≤ 1     (saturable by id)   │
  │ cross-swap  (3/2, 1/2)   │ f(1) ≤ 1                         │
  │ collapse-lo (1/2, 1/2)   │ f(1) ≤ 1/2                       │
  │ collapse-hi (3/2, 3/2)   │ f(1) ≤ 3/2                       │
  └──────────────────────────┴──────────────────────────────────┘

This is NOT a refutation of any pairing — every pairing remains
realisable in principle. It is an OFF-CLUSTER UPPER BOUND on the
value `f(1)` at the cluster spectral midpoint, which any midpoint-
convex `f` realising the pairing MUST satisfy.

Verdict: OFF-CLUSTER CONSTRAINT, not refutation. Distinct from:

  * Wave 26 (polynomial Sylvester) — operator-level positive
    realisations of all 4 pairings.
  * Wave 29 (Padé [1/1]), Wave 30 (two-pole Stieltjes) — functional-
    level IN, operator-level OUT via Cayley–Hamilton collapse.
  * Wave 31 (operator-monotone / Loewner) — ON-CLUSTER refutation
    of the cross-swap pairing.
  * Wave 32 (operator-convex / midpoint, this file) — OFF-CLUSTER
    upper bound on `f(1)` at the cluster spectral midpoint, applies
    to all 4 pairings uniformly. -/

/-- **★★★ Operator-convex / midpoint-convex canonical-construction
    imposes OFF-CLUSTER upper bounds on `f(1)` at the cluster
    spectral midpoint for all 4 Wave 24 pairings — strategic
    capstone** (axiom-free).

    The cluster spectral midpoint `λ = (1/2 + 3/2)/2 = 1` lies in
    the SPECTRAL GAP between the two cluster eigenvalues `{1/2,
    3/2}`. For every midpoint-convex `f : ℝ → ℝ` realising a
    Wave 24 cluster pairing, the OFF-CLUSTER value `f(1)` is bounded
    above by the arithmetic mean of the cluster IMAGES:

      (a) Pointwise   (1/2, 3/2) → f(1) ≤ 1
      (b) Cross-swap  (3/2, 1/2) → f(1) ≤ 1
      (c) Collapse-lo (1/2, 1/2) → f(1) ≤ 1/2
      (d) Collapse-hi (3/2, 3/2) → f(1) ≤ 3/2

    Plus (e): the identity `f(x) = x` is a POSITIVE WITNESS — it is
    midpoint-convex, realises the pointwise pairing, and saturates
    the pointwise off-cluster bound with `f(1) = 1`.

    Honest scope: this is NOT a refutation of any pairing. Every
    pairing remains realisable in principle. The result is an
    OFF-CLUSTER UPPER BOUND that any midpoint-convex realisation
    MUST satisfy — a genuinely new KIND of structural constraint
    (off-cluster, not on-cluster) in the Wave 26+ YM canonical-
    operator taxonomy. Operator-convexity (Hansen–Pedersen 1982)
    implies midpoint convexity on the scalar restriction (1×1
    matrices), so this scalar bound is INHERITED by every operator-
    convex candidate, regardless of its specific Stieltjes-measure
    representation.

    Wave 26-32 status summary:
    Wave 26 polynomial IN (operator-level, all 4 pairings);
    Wave 29 Padé [1/1] functional-IN / operator-OUT;
    Wave 30 two-pole Stieltjes functional-IN / operator-OUT;
    Wave 31 operator-monotone PARTIAL (cross-swap on-cluster
            STRUCTURALLY REFUTED, pointwise IN strict, collapses
            IN degenerate);
    **Wave 32 operator-convex / midpoint OFF-CLUSTER CONSTRAINT**
            (this file): all 4 pairings still IN, but each subject
            to an off-cluster upper bound on `f(1)` at the cluster
            spectral midpoint `λ = 1`. -/
theorem ym_canonical_convex_imposes_off_cluster_bounds_at_one :
    -- (a) Pointwise: midpoint-convex realisations satisfy f(1) ≤ 1.
    (∀ f : ℝ → ℝ, MidpointConvex f →
       f (1/2) = 1/2 → f (3/2) = 3/2 → f 1 ≤ 1) ∧
    -- (b) Cross-swap: midpoint-convex realisations satisfy f(1) ≤ 1.
    (∀ f : ℝ → ℝ, MidpointConvex f →
       f (1/2) = 3/2 → f (3/2) = 1/2 → f 1 ≤ 1) ∧
    -- (c) Collapse-low: midpoint-convex realisations satisfy
    --     f(1) ≤ 1/2.
    (∀ f : ℝ → ℝ, MidpointConvex f →
       f (1/2) = 1/2 → f (3/2) = 1/2 → f 1 ≤ 1/2) ∧
    -- (d) Collapse-high: midpoint-convex realisations satisfy
    --     f(1) ≤ 3/2.
    (∀ f : ℝ → ℝ, MidpointConvex f →
       f (1/2) = 3/2 → f (3/2) = 3/2 → f 1 ≤ 3/2) ∧
    -- (e) POSITIVE WITNESS: the identity `f(x) = x` is midpoint-
    --     convex, realises the pointwise pairing, and saturates
    --     the pointwise off-cluster bound `f(1) = 1`.
    (MidpointConvex idMap ∧
     idMap (1/2) = 1/2 ∧
     idMap (3/2) = 3/2 ∧
     idMap 1 = 1 ∧
     idMap 1 ≤ 1) :=
  ⟨midpoint_convex_pointwise_off_cluster_bound,
   midpoint_convex_cross_swap_off_cluster_bound,
   midpoint_convex_collapse_low_off_cluster_bound,
   midpoint_convex_collapse_high_off_cluster_bound,
   idMap_realises_pointwise_and_saturates_bound⟩

/-! ## Part 7 — Axiom-freeness verification -/

#print axioms cluster_arithmetic_midpoint
#print axioms midpoint_convex_cluster_midpoint_bound
#print axioms midpoint_convex_pointwise_off_cluster_bound
#print axioms midpoint_convex_cross_swap_off_cluster_bound
#print axioms midpoint_convex_collapse_low_off_cluster_bound
#print axioms midpoint_convex_collapse_high_off_cluster_bound
#print axioms idMap_midpoint_convex
#print axioms idMap_at_half
#print axioms idMap_at_three_halves
#print axioms idMap_at_one
#print axioms idMap_saturates_pointwise_off_cluster_bound
#print axioms idMap_realises_pointwise_and_saturates_bound
#print axioms ym_canonical_convex_imposes_off_cluster_bounds_at_one

end PrincipiaTractalis

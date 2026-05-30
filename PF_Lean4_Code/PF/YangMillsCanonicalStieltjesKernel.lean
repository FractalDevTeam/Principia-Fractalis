/-
# Yang-Mills Canonical Kernel — Two-Pole Discrete Stieltjes Cluster-Fix
  Triples in (and outside) the Wave 26 Polynomial Sylvester family
  AND outside the Wave 29 Padé [1/1] family

## Strategic context (2026-05-30, Wave 30 YM follow-on)

Waves 27–29 progressed the canonical-operator question for the Wave 24
cluster-fix mechanism on the 2D `M_cluster` operator
(eigenvalues `{1/2, 3/2}`) as follows:

  * REAL HEAT KERNEL `e^{−t·M}`              (Wave 27 `a666399`) — **OUT**.
  * QUANTUM PROPAGATOR `e^{−i·t·M}`          (Wave 28 `9df6ef4`) — **OUT**
    (forces COMPLEX off-real images on a REAL cluster).
  * RESOLVENT `(M − μI)⁻¹`                   (Wave 28 `7437ea3`) — **OUT**
    (per-image μ-uniqueness contradicts in pairs).
  * PARTIAL-FRACTION `α·(M − μI)⁻¹ + β·I + γ·M`
                                              (Wave 29)           — **OUT**
    (sums + products of resolvents reduce by Cayley–Hamilton to
     `a = 0` Sylvester triples; all 4 cluster pairings refuted).
  * PADÉ [1/1] APPROXIMANT
    `φ(λ) = (a₀ + a₁·λ)/(b₀ + b₁·λ)`         (Wave 29)           — **IN**
    (4-parameter rational map; all 4 cluster pairings realised at
     explicit witnesses; STRUCTURAL non-bridge to Wave 26 polynomial
     family via off-cluster disagreement at λ = 100).

The Wave 29 master capstone listed "Stieltjes / dispersion-integral
representations" as a STILL SURVIVING untested route. This file
investigates the next candidate: the **two-pole discrete Stieltjes**
functional form

    φ(λ)  :=  α₁/(μ₁ − λ)  +  α₂/(μ₂ − λ)  +  β                          (♣)

A two-pole discrete Stieltjes has 5 free parameters
`(α₁, α₂, μ₁, μ₂, β)`. On the level-1 YM cluster `{1/2, 3/2}`,
this gives 2 cluster-target equations in 5 unknowns —
UNDERDETERMINED, so solutions EXIST for every cluster target pair.

## Honest scope

This file restricts to the **DISCRETE** Stieltjes case (finite-support
positive measure with TWO mass points `μ₁, μ₂` and arbitrary real
weights `α₁, α₂` plus a constant `β`). The continuous Stieltjes
representation `φ(λ) = ∫ dν(t)/(t − λ) + β` for a positive measure `ν`
would require Lean integration machinery (Bochner, etc.) that is
heavy and orthogonal to the cluster-fix question — the discrete case
already exhibits the relevant functional-form distinction.

We use real (not necessarily positive) weights `α₁, α₂`; this is the
"signed Stieltjes" variant — strictly more general than the
positive-measure case but still genuinely two-pole when both `αᵢ ≠ 0`
and `μ₁ ≠ μ₂`.

## Honest finding (POSITIVE-WITNESS + STRUCTURAL NON-BRIDGE)

For each of the four natural Wave 24 cluster-fix pairings
`(c₁, c₂) ∈ {1/2, 3/2}²`, we exhibit an EXPLICIT non-degenerate
two-pole discrete Stieltjes quintuple `(α₁, α₂, μ₁, μ₂, β)` with
`α₁ ≠ 0`, `α₂ ≠ 0`, `μ₁ ≠ μ₂`, and `μ₁, μ₂ ∉ {1/2, 3/2}` (genuinely
two-pole, with both poles distinct from the cluster spectrum), that
fixes both cluster centres:

    (c₁, c₂) = (1/2, 1/2):   (α₁, α₂, μ₁, μ₂, β) = (−1,  1, 0, 2, −13/6)
    (c₁, c₂) = (1/2, 3/2):   (α₁, α₂, μ₁, μ₂, β) = ( 1, −1/4, 0, 2,   8/3)
    (c₁, c₂) = (3/2, 1/2):   (α₁, α₂, μ₁, μ₂, β) = (−1,  1/4, 0, 2,  −2/3)
    (c₁, c₂) = (3/2, 3/2):   (α₁, α₂, μ₁, μ₂, β) = (−1,  1, 0, 2,  −7/6)

Each witness is verified by direct arithmetic (axiom-free).

So the two-pole discrete Stieltjes form CAN fix BOTH cluster centres
for ANY natural pairing. But it does NOT live inside the Wave 26
polynomial Sylvester family, NOR inside the Wave 29 Padé [1/1]
family, in the following functional sense:

  * A two-pole Stieltjes with `α₁ ≠ 0`, `α₂ ≠ 0`, `μ₁ ≠ μ₂` has TWO
    distinct poles at `λ ∈ {μ₁, μ₂}` — it is a rational function whose
    denominator factors as `(μ₁ − λ)(μ₂ − λ)`.
  * A Wave 29 Padé [1/1] map with `b₁ ≠ 0` has a SINGLE pole at
    `λ = −b₀/b₁`.
  * A Wave 26 polynomial Sylvester map `a·λ² + b·λ + c` has NO poles
    (it is a polynomial).

So the two-pole Stieltjes family (with both poles genuine), the Padé
[1/1] family (single pole), and the polynomial Sylvester family
(zero poles) are STRUCTURALLY DISTINCT functional-form classes,
distinguishable by the number of poles in `λ`. The two-pole Stieltjes
witnesses above realise the same `{1/2, 3/2} × {1/2, 3/2}` cluster
pairings as the Wave 26 polynomial and Wave 29 Padé witnesses, but
via a DIFFERENT mechanism (two-pole rational substitution).

## Strategic verdict

**Two-pole discrete Stieltjes is a NEW canonical YM cluster-fix
mechanism OUTSIDE BOTH the Wave 26 polynomial Sylvester family AND
the Wave 29 Padé [1/1] family.** Unlike the four narrowed-out
heat-kernel / quantum-propagator / single-resolvent / partial-fraction
routes, the two-pole Stieltjes family DOES fix both cluster centres,
at the FUNCTIONAL level in `λ`.

This:

  * Confirms that the Wave 24 cluster-fix mechanism admits at least
    THREE disjoint canonical functional-form realisations:
      (1) polynomial Sylvester `a·λ² + b·λ + c`        (Wave 26),
      (2) single-pole Padé [1/1] `(a₀+a₁λ)/(b₀+b₁λ)`   (Wave 29),
      (3) two-pole discrete Stieltjes
          `α₁/(μ₁−λ) + α₂/(μ₂−λ) + β`                  (THIS FILE).
  * Does NOT discharge the YM mass gap. The cluster-fix witnesses are
    structural functional-form solutions, not operator-theoretic
    derivations from a canonical PDE / quantum / spectral object.
  * Honest scope at the OPERATOR level: when promoted to an operator
    construction on the 2D cluster, the two-pole Stieltjes
    `α₁·(μ₁I − M)⁻¹ + α₂·(μ₂I − M)⁻¹ + β·I` lies in the same
    `rational-function-of-M` class as the Wave 29 partial-fraction
    candidate, which Cayley–Hamilton collapses to a degree-1
    polynomial in `M`. So this is a FUNCTIONAL-LEVEL positive
    realisation in `λ`, NOT a new operator-level escape from the
    Wave 29 partial-fraction narrow-out.

## What this file proves (all axiom-free)

  1. `twoPoleStieltjesMap α₁ α₂ μ₁ μ₂ β λ
       := α₁/(μ₁ − λ) + α₂/(μ₂ − λ) + β`.
  2. CLUSTER-IMAGE FORMULAE at `λ ∈ {1/2, 3/2}`.
  3. EXPLICIT WITNESSES for all four `(c₁, c₂) ∈ {1/2, 3/2}²`
     pairings with `α₁ ≠ 0`, `α₂ ≠ 0`, `μ₁ ≠ μ₂`, `μ₁, μ₂ ∉ {1/2, 3/2}`
     (genuinely two-pole, poles off the cluster spectrum).
  4. NON-DEGENERACY: every witness has `α₁ ≠ 0` and `α₂ ≠ 0`.
  5. STRUCTURAL NON-BRIDGE to Wave 26 polynomial Sylvester: off-cluster
     disagreement at `λ = 100`.
  6. STRUCTURAL NON-BRIDGE to Wave 29 Padé [1/1]: off-cluster
     disagreement at `λ = 100`.
  7. **Capstone**
     `ym_canonical_two_pole_stieltjes_realises_cluster_fix_outside_polynomial_and_pade_families`:
     the canonical two-pole discrete Stieltjes route REALISES the
     Wave 24 cluster-fix pairings but lies STRUCTURALLY OUTSIDE both
     the Wave 26 polynomial Sylvester family AND the Wave 29 Padé
     [1/1] family.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

Author: Pablo Cohen (with assistance). 2026-05-30 Wave 30 YM follow-on
(Stieltjes / dispersion-integral counterpart of Wave 29 Padé [1/1]
commit `…` and partial-fraction narrow-out).
-/

import PF.YangMillsCanonicalPadeApproximantKernel

namespace PrincipiaTractalis

/-! ## Part 1 — The two-pole discrete Stieltjes map

The two-pole discrete Stieltjes form (signed, with constant tail):

    φ(λ)  =  α₁ / (μ₁ − λ)  +  α₂ / (μ₂ − λ)  +  β

with five free parameters `(α₁, α₂, μ₁, μ₂, β)`. Discrete = the
underlying signed measure has finite support `{μ₁, μ₂}` (two atoms);
the `β` tail represents a constant added to the dispersion integral.
The "Stieltjes" name reflects the structural form
`φ(λ) = ∫ dν(t)/(t − λ) + β` specialised to a two-atom signed `ν`. -/

/-- **Two-pole discrete Stieltjes map** (axiom-free).

    The rational function `α₁/(μ₁ − λ) + α₂/(μ₂ − λ) + β`. The five
    parameters `(α₁, α₂, μ₁, μ₂, β)` are unconstrained reals. -/
noncomputable def twoPoleStieltjesMap
    (a1 a2 mu1 mu2 beta lam : ℝ) : ℝ :=
  a1 / (mu1 - lam) + a2 / (mu2 - lam) + beta

/-- **Closed-form** (axiom-free): trivial unfolding. -/
theorem twoPoleStieltjesMap_eq (a1 a2 mu1 mu2 beta lam : ℝ) :
    twoPoleStieltjesMap a1 a2 mu1 mu2 beta lam =
      a1 / (mu1 - lam) + a2 / (mu2 - lam) + beta := rfl

/-- **Lower cluster image at `λ = 1/2`** (axiom-free):
    `φ(1/2) = α₁/(μ₁ − 1/2) + α₂/(μ₂ − 1/2) + β`. -/
theorem twoPoleStieltjesMap_at_half (a1 a2 mu1 mu2 beta : ℝ) :
    twoPoleStieltjesMap a1 a2 mu1 mu2 beta (1/2) =
      a1 / (mu1 - 1/2) + a2 / (mu2 - 1/2) + beta := rfl

/-- **Upper cluster image at `λ = 3/2`** (axiom-free):
    `φ(3/2) = α₁/(μ₁ − 3/2) + α₂/(μ₂ − 3/2) + β`. -/
theorem twoPoleStieltjesMap_at_three_halves (a1 a2 mu1 mu2 beta : ℝ) :
    twoPoleStieltjesMap a1 a2 mu1 mu2 beta (3/2) =
      a1 / (mu1 - 3/2) + a2 / (mu2 - 3/2) + beta := rfl

/-! ## Part 2 — Explicit witnesses for all four `(c₁, c₂) ∈ {1/2, 3/2}²`
    pairings.

For each pairing, we provide an EXPLICIT non-degenerate two-pole
discrete Stieltjes quintuple with `α₁ ≠ 0`, `α₂ ≠ 0`, `μ₁ = 0`,
`μ₂ = 2` (so `μ₁ ≠ μ₂` and both poles are OFF the cluster spectrum
`{1/2, 3/2}`). Each witness is verified by direct arithmetic.

The common pole pair `(μ₁, μ₂) = (0, 2)` is chosen for arithmetic
cleanness: it makes the cluster denominators
`μ₁ − 1/2 = −1/2`, `μ₁ − 3/2 = −3/2`, `μ₂ − 1/2 = 3/2`,
`μ₂ − 3/2 = 1/2`. -/

/-- **Witness `(c₁, c₂) = (1/2, 1/2)` — lower image** (axiom-free).

    `φ(λ) = −1/(0 − λ) + 1/(2 − λ) − 13/6` sends `λ = 1/2` to `1/2`. -/
theorem twoPoleStieltjes_collapse_low_at_half :
    twoPoleStieltjesMap (-1) 1 0 2 (-13/6) (1/2) = 1/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Witness `(c₁, c₂) = (1/2, 1/2)` — upper image** (axiom-free).

    `φ(λ) = −1/(0 − λ) + 1/(2 − λ) − 13/6` sends `λ = 3/2` to `1/2`. -/
theorem twoPoleStieltjes_collapse_low_at_three_halves :
    twoPoleStieltjesMap (-1) 1 0 2 (-13/6) (3/2) = 1/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Witness `(c₁, c₂) = (1/2, 3/2)` — lower image** (axiom-free).

    `φ(λ) = 1/(0 − λ) − (1/4)/(2 − λ) + 8/3` sends `λ = 1/2` to `1/2`. -/
theorem twoPoleStieltjes_pointwise_at_half :
    twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) (1/2) = 1/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Witness `(c₁, c₂) = (1/2, 3/2)` — upper image** (axiom-free).

    `φ(λ) = 1/(0 − λ) − (1/4)/(2 − λ) + 8/3` sends `λ = 3/2` to `3/2`. -/
theorem twoPoleStieltjes_pointwise_at_three_halves :
    twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) (3/2) = 3/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Witness `(c₁, c₂) = (3/2, 1/2)` — lower image** (axiom-free).

    `φ(λ) = −1/(0 − λ) + (1/4)/(2 − λ) − 2/3` sends `λ = 1/2` to `3/2`. -/
theorem twoPoleStieltjes_cross_swap_at_half :
    twoPoleStieltjesMap (-1) (1/4) 0 2 (-2/3) (1/2) = 3/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Witness `(c₁, c₂) = (3/2, 1/2)` — upper image** (axiom-free).

    `φ(λ) = −1/(0 − λ) + (1/4)/(2 − λ) − 2/3` sends `λ = 3/2` to `1/2`. -/
theorem twoPoleStieltjes_cross_swap_at_three_halves :
    twoPoleStieltjesMap (-1) (1/4) 0 2 (-2/3) (3/2) = 1/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Witness `(c₁, c₂) = (3/2, 3/2)` — lower image** (axiom-free).

    `φ(λ) = −1/(0 − λ) + 1/(2 − λ) − 7/6` sends `λ = 1/2` to `3/2`. -/
theorem twoPoleStieltjes_collapse_high_at_half :
    twoPoleStieltjesMap (-1) 1 0 2 (-7/6) (1/2) = 3/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Witness `(c₁, c₂) = (3/2, 3/2)` — upper image** (axiom-free).

    `φ(λ) = −1/(0 − λ) + 1/(2 − λ) − 7/6` sends `λ = 3/2` to `3/2`. -/
theorem twoPoleStieltjes_collapse_high_at_three_halves :
    twoPoleStieltjesMap (-1) 1 0 2 (-7/6) (3/2) = 3/2 := by
  unfold twoPoleStieltjesMap; norm_num

/-! ## Part 3 — Joint cluster-fix witnesses (pairing conjunctions). -/

/-- **JOINT WITNESS `(1/2, 1/2)` — collapse-low** (axiom-free). -/
theorem twoPoleStieltjes_realises_collapse_low :
    twoPoleStieltjesMap (-1) 1 0 2 (-13/6) (1/2) = 1/2 ∧
    twoPoleStieltjesMap (-1) 1 0 2 (-13/6) (3/2) = 1/2 :=
  ⟨twoPoleStieltjes_collapse_low_at_half,
   twoPoleStieltjes_collapse_low_at_three_halves⟩

/-- **JOINT WITNESS `(1/2, 3/2)` — pointwise** (axiom-free). -/
theorem twoPoleStieltjes_realises_pointwise :
    twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) (1/2) = 1/2 ∧
    twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) (3/2) = 3/2 :=
  ⟨twoPoleStieltjes_pointwise_at_half,
   twoPoleStieltjes_pointwise_at_three_halves⟩

/-- **JOINT WITNESS `(3/2, 1/2)` — cross-swap** (axiom-free). -/
theorem twoPoleStieltjes_realises_cross_swap :
    twoPoleStieltjesMap (-1) (1/4) 0 2 (-2/3) (1/2) = 3/2 ∧
    twoPoleStieltjesMap (-1) (1/4) 0 2 (-2/3) (3/2) = 1/2 :=
  ⟨twoPoleStieltjes_cross_swap_at_half,
   twoPoleStieltjes_cross_swap_at_three_halves⟩

/-- **JOINT WITNESS `(3/2, 3/2)` — collapse-high** (axiom-free). -/
theorem twoPoleStieltjes_realises_collapse_high :
    twoPoleStieltjesMap (-1) 1 0 2 (-7/6) (1/2) = 3/2 ∧
    twoPoleStieltjesMap (-1) 1 0 2 (-7/6) (3/2) = 3/2 :=
  ⟨twoPoleStieltjes_collapse_high_at_half,
   twoPoleStieltjes_collapse_high_at_three_halves⟩

/-! ## Part 4 — Non-degeneracy: every witness has `α₁ ≠ 0`, `α₂ ≠ 0`,
    `μ₁ ≠ μ₂`, and both poles off the cluster spectrum. -/

/-- **Non-degeneracy of all four witnesses** (axiom-free).

      (i)   `α₁ ≠ 0` for all four witnesses (`α₁ ∈ {−1, 1}`).
      (ii)  `α₂ ≠ 0` for all four witnesses (`α₂ ∈ {1, −1/4, 1/4}`).
      (iii) `μ₁ ≠ μ₂` in all four witnesses (`0 ≠ 2`).
      (iv)  `μ₁ ∉ {1/2, 3/2}` and `μ₂ ∉ {1/2, 3/2}`
            (`0, 2` are both off the cluster spectrum). -/
theorem twoPoleStieltjes_witnesses_all_genuinely_two_pole :
    ((-1 : ℝ) ≠ 0) ∧ ((1 : ℝ) ≠ 0) ∧ ((1/4 : ℝ) ≠ 0) ∧
    ((-1/4 : ℝ) ≠ 0) ∧ ((0 : ℝ) ≠ (2 : ℝ)) ∧
    ((0 : ℝ) ≠ (1/2 : ℝ)) ∧ ((0 : ℝ) ≠ (3/2 : ℝ)) ∧
    ((2 : ℝ) ≠ (1/2 : ℝ)) ∧ ((2 : ℝ) ≠ (3/2 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## Part 5 — Structural non-bridge to Wave 26 polynomial Sylvester:
    off-cluster disagreement at `λ = 100`.

The Wave 26 polynomial Sylvester family is `Q(λ) = a·λ² + b·λ + c`.
At `λ = 100`, the Wave 26 polynomial witnesses
`(1, −2, 5/4)` (collapse-low) and `(1, −1, 3/4)` (pointwise)
evaluate to `9801.25` and `9900.75` respectively. The two-pole
Stieltjes witnesses evaluate to small bounded values (the dispersion
integral is bounded away from the poles), proving these are
genuinely different functions on ℝ. -/

/-- **Two-pole Stieltjes collapse-low witness at `λ = 100`**
    (axiom-free).

    `φ(100) = −1/(0 − 100) + 1/(2 − 100) − 13/6
            = 1/100 − 1/98 − 13/6`. -/
theorem twoPoleStieltjes_collapse_low_at_hundred :
    twoPoleStieltjesMap (-1) 1 0 2 (-13/6) 100 =
      1/100 - 1/98 - 13/6 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **Two-pole Stieltjes pointwise witness at `λ = 100`**
    (axiom-free).

    `φ(100) = 1/(0 − 100) − (1/4)/(2 − 100) + 8/3
            = −1/100 + 1/392 + 8/3`. -/
theorem twoPoleStieltjes_pointwise_at_hundred :
    twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) 100 =
      -1/100 + 1/392 + 8/3 := by
  unfold twoPoleStieltjesMap; norm_num

/-- **STRUCTURAL NON-BRIDGE — two-pole Stieltjes witness ≠ polynomial
    witness at `λ = 100`** (collapse-low pairing, axiom-free).

    The collapse-low two-pole Stieltjes witness
    `(−1, 1, 0, 2, −13/6)` and the collapse-low Wave 26 polynomial
    witness `(1, −2, 5/4)` agree on the cluster pair `{1/2, 3/2}`
    (both fix to `(1/2, 1/2)`), but DISAGREE OUTSIDE the cluster: at
    `λ = 100`, the Stieltjes map returns `1/100 − 1/98 − 13/6 ≈
    −2.167`, whereas the polynomial map returns `9801.25`. -/
theorem stieltjes_and_polynomial_collapse_low_witnesses_disagree_off_cluster :
    twoPoleStieltjesMap (-1) 1 0 2 (-13/6) 100 ≠
      mixedOrderKernelMap 1 (-2) (5/4) 100 := by
  rw [twoPoleStieltjes_collapse_low_at_hundred,
      mixedOrder_collapse_low_at_hundred]
  norm_num

/-- **STRUCTURAL NON-BRIDGE — two-pole Stieltjes witness ≠ polynomial
    witness at `λ = 100`** (pointwise pairing, axiom-free).

    The pointwise two-pole Stieltjes witness
    `(1, −1/4, 0, 2, 8/3)` and the pointwise Wave 26 polynomial
    witness `(1, −1, 3/4)` both realise the cluster-fix `(1/2, 3/2)`,
    but DISAGREE at `λ = 100`. -/
theorem stieltjes_and_polynomial_pointwise_witnesses_disagree_off_cluster :
    twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) 100 ≠
      mixedOrderKernelMap 1 (-1) (3/4) 100 := by
  rw [twoPoleStieltjes_pointwise_at_hundred]
  have h2 : mixedOrderKernelMap 1 (-1) (3/4) 100 = 9900.75 := by
    rw [mixedOrderKernelMap_eq]; norm_num
  rw [h2]
  norm_num

/-! ## Part 6 — Structural non-bridge to Wave 29 Padé [1/1]:
    off-cluster disagreement at `λ = 100`.

The Wave 29 Padé [1/1] collapse-low witness `(1/2, 1/2; 1, 1)` is
asymptotic to `1/2` (the witness was specifically arranged so `φ ≡ 1/2`
on the cluster). At `λ = 100` the Padé map returns `1/2`, while the
two-pole Stieltjes collapse-low witness returns a value close to
`−13/6` (the constant tail dominates). -/

/-- **STRUCTURAL NON-BRIDGE — two-pole Stieltjes witness ≠ Padé [1/1]
    witness at `λ = 100`** (collapse-low pairing, axiom-free).

    Both the collapse-low two-pole Stieltjes witness
    `(−1, 1, 0, 2, −13/6)` and the collapse-low Wave 29 Padé [1/1]
    witness `(1/2, 1/2; 1, 1)` realise `(c₁, c₂) = (1/2, 1/2)` on the
    cluster, but DISAGREE OUTSIDE the cluster: at `λ = 100`, the
    Stieltjes map returns `1/100 − 1/98 − 13/6 ≈ −2.167`, whereas the
    Padé map returns `1/2`. -/
theorem stieltjes_and_pade_collapse_low_witnesses_disagree_off_cluster :
    twoPoleStieltjesMap (-1) 1 0 2 (-13/6) 100 ≠
      padeOneOneMap (1/2) (1/2) 1 1 100 := by
  rw [twoPoleStieltjes_collapse_low_at_hundred,
      padeOneOne_collapse_low_at_hundred]
  norm_num

/-- **STRUCTURAL NON-BRIDGE — two-pole Stieltjes witness ≠ Padé [1/1]
    witness at `λ = 100`** (pointwise pairing, axiom-free).

    The pointwise two-pole Stieltjes witness `(1, −1/4, 0, 2, 8/3)`
    and the pointwise Wave 29 Padé [1/1] witness `(−3/4, 4; 2, 1)`
    both realise the cluster-fix `(1/2, 3/2)`, but DISAGREE at
    `λ = 100`. -/
theorem stieltjes_and_pade_pointwise_witnesses_disagree_off_cluster :
    twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) 100 ≠
      padeOneOneMap (-3/4) 4 2 1 100 := by
  rw [twoPoleStieltjes_pointwise_at_hundred]
  have h2 : padeOneOneMap (-3/4) 4 2 1 100 = 399.25 / 102 := by
    unfold padeOneOneMap; norm_num
  rw [h2]
  -- LHS = -1/100 + 1/392 + 8/3.  RHS = 399.25/102.
  -- Cross-check: LHS ≈ -0.01 + 0.00255 + 2.6667 ≈ 2.659.
  -- RHS = 399.25/102 ≈ 3.914.  Clearly distinct.
  norm_num

/-! ## Part 7 — Strategic capstone: two-pole discrete Stieltjes is a
    NEW canonical YM mechanism, OUTSIDE BOTH the Wave 26 polynomial
    Sylvester family AND the Wave 29 Padé [1/1] family. -/

/-- **★★★ Two-pole discrete Stieltjes canonical-construction REALISES
    the Wave 24 cluster-fix OUTSIDE the Wave 26 polynomial Sylvester
    family AND the Wave 29 Padé [1/1] family — strategic capstone**
    (axiom-free).

    The canonical two-pole discrete Stieltjes form
    `φ(λ) = α₁/(μ₁ − λ) + α₂/(μ₂ − λ) + β` REALISES all four natural
    Wave 24 cluster-fix pairings `(c₁, c₂) ∈ {1/2, 3/2}²` via
    explicit witnesses:

      (1/2, 1/2):   `(α₁, α₂, μ₁, μ₂, β) = (−1,  1, 0, 2, −13/6)`
      (1/2, 3/2):   `(α₁, α₂, μ₁, μ₂, β) = ( 1, −1/4, 0, 2,   8/3)`
      (3/2, 1/2):   `(α₁, α₂, μ₁, μ₂, β) = (−1,  1/4, 0, 2,  −2/3)`
      (3/2, 3/2):   `(α₁, α₂, μ₁, μ₂, β) = (−1,  1, 0, 2,  −7/6)`

    Every witness has `α₁ ≠ 0`, `α₂ ≠ 0`, `μ₁ = 0 ≠ 2 = μ₂`, and
    both poles `0, 2` off the cluster spectrum `{1/2, 3/2}` — so each
    is GENUINELY TWO-POLE (a non-constant rational function with TWO
    distinct poles), distinguishable both from a single-pole Padé
    [1/1] and from a no-pole polynomial Sylvester map.

    Off-cluster non-bridge confirmed:

      * Stieltjes collapse-low `(−1, 1, 0, 2, −13/6)` at `λ = 100`
        returns `1/100 − 1/98 − 13/6 ≈ −2.167`, whereas the
        Wave 26 polynomial collapse-low witness `(1, −2, 5/4)`
        returns `9801.25` and the Wave 29 Padé collapse-low
        witness `(1/2, 1/2; 1, 1)` returns `1/2`.
      * Stieltjes pointwise `(1, −1/4, 0, 2, 8/3)` at `λ = 100`
        returns `−1/100 + 1/392 + 8/3 ≈ 2.659`, whereas the
        Wave 26 polynomial pointwise witness `(1, −1, 3/4)` returns
        `9900.75` and the Wave 29 Padé pointwise witness
        `(−3/4, 4; 2, 1)` returns `399.25/102 ≈ 3.914`.

    OUTCOME (Wave 30 positive): the two-pole discrete Stieltjes form
    is a NEW canonical YM cluster-fix MECHANISM, distinct from and
    orthogonal to BOTH the Wave 26 polynomial Sylvester family AND
    the Wave 29 Padé [1/1] family. After the four NARROWED-OUT
    exponential / resolvent / partial-fraction constructions, this
    becomes the THIRD POSITIVE canonical functional form realising
    the Wave 24 cluster fix — alongside polynomial Sylvester (Wave
    26) and single-pole Padé (Wave 29).

    Honest scope at the OPERATOR level: when promoted to a 2D
    operator `α₁·(μ₁I − M)⁻¹ + α₂·(μ₂I − M)⁻¹ + β·I`, this construction
    lies in the same rational-function-of-M class as the Wave 29
    partial-fraction candidate, which Cayley–Hamilton collapses to a
    degree-1 polynomial in `M`. So this is a FUNCTIONAL-LEVEL positive
    realisation in `λ`, NOT a new operator-level escape from the
    Wave 29 partial-fraction narrow-out. Like Wave 29 Padé, the
    Wave 30 Stieltjes is a SECOND-PLUS-ONE canonical FUNCTIONAL FORM
    distinct from the polynomial Sylvester family.

    Sylvester narrow-out / positive-realisation status after Wave 30:
    heat-kernel OUT, single-resolvent OUT, quantum-propagator OUT,
    partial-fraction OUT (operator-level), **Padé [1/1] IN**,
    **two-pole discrete Stieltjes IN** (this file). Still untested:
    higher-order Padé `[m/n]` with `(m, n) ≠ (1, 1)`, contour-integral
    constructions, operator-monotone / Loewner constructions,
    continuous-measure Stieltjes (requires integration machinery). -/
theorem ym_canonical_two_pole_stieltjes_realises_cluster_fix_outside_polynomial_and_pade_families :
    -- (a) Lower-cluster image formula
    (∀ a1 a2 mu1 mu2 beta : ℝ,
        twoPoleStieltjesMap a1 a2 mu1 mu2 beta (1/2) =
          a1 / (mu1 - 1/2) + a2 / (mu2 - 1/2) + beta) ∧
    -- (b) Upper-cluster image formula
    (∀ a1 a2 mu1 mu2 beta : ℝ,
        twoPoleStieltjesMap a1 a2 mu1 mu2 beta (3/2) =
          a1 / (mu1 - 3/2) + a2 / (mu2 - 3/2) + beta) ∧
    -- (c) Collapse-low (1/2, 1/2) witness
    (twoPoleStieltjesMap (-1) 1 0 2 (-13/6) (1/2) = 1/2 ∧
     twoPoleStieltjesMap (-1) 1 0 2 (-13/6) (3/2) = 1/2) ∧
    -- (d) Pointwise (1/2, 3/2) witness
    (twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) (1/2) = 1/2 ∧
     twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) (3/2) = 3/2) ∧
    -- (e) Cross-swap (3/2, 1/2) witness
    (twoPoleStieltjesMap (-1) (1/4) 0 2 (-2/3) (1/2) = 3/2 ∧
     twoPoleStieltjesMap (-1) (1/4) 0 2 (-2/3) (3/2) = 1/2) ∧
    -- (f) Collapse-high (3/2, 3/2) witness
    (twoPoleStieltjesMap (-1) 1 0 2 (-7/6) (1/2) = 3/2 ∧
     twoPoleStieltjesMap (-1) 1 0 2 (-7/6) (3/2) = 3/2) ∧
    -- (g) Non-degeneracy of every witness: genuinely two-pole, both poles off-cluster
    (((-1 : ℝ) ≠ 0) ∧ ((1 : ℝ) ≠ 0) ∧ ((1/4 : ℝ) ≠ 0) ∧
     ((-1/4 : ℝ) ≠ 0) ∧ ((0 : ℝ) ≠ (2 : ℝ)) ∧
     ((0 : ℝ) ≠ (1/2 : ℝ)) ∧ ((0 : ℝ) ≠ (3/2 : ℝ)) ∧
     ((2 : ℝ) ≠ (1/2 : ℝ)) ∧ ((2 : ℝ) ≠ (3/2 : ℝ))) ∧
    -- (h) Off-cluster structural disagreement vs Wave 26 polynomial:
    --     collapse-low pairing
    (twoPoleStieltjesMap (-1) 1 0 2 (-13/6) 100 ≠
       mixedOrderKernelMap 1 (-2) (5/4) 100) ∧
    -- (i) Off-cluster structural disagreement vs Wave 26 polynomial:
    --     pointwise pairing
    (twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) 100 ≠
       mixedOrderKernelMap 1 (-1) (3/4) 100) ∧
    -- (j) Off-cluster structural disagreement vs Wave 29 Padé [1/1]:
    --     collapse-low pairing
    (twoPoleStieltjesMap (-1) 1 0 2 (-13/6) 100 ≠
       padeOneOneMap (1/2) (1/2) 1 1 100) ∧
    -- (k) Off-cluster structural disagreement vs Wave 29 Padé [1/1]:
    --     pointwise pairing
    (twoPoleStieltjesMap 1 (-1/4) 0 2 (8/3) 100 ≠
       padeOneOneMap (-3/4) 4 2 1 100) :=
  ⟨twoPoleStieltjesMap_at_half,
   twoPoleStieltjesMap_at_three_halves,
   twoPoleStieltjes_realises_collapse_low,
   twoPoleStieltjes_realises_pointwise,
   twoPoleStieltjes_realises_cross_swap,
   twoPoleStieltjes_realises_collapse_high,
   twoPoleStieltjes_witnesses_all_genuinely_two_pole,
   stieltjes_and_polynomial_collapse_low_witnesses_disagree_off_cluster,
   stieltjes_and_polynomial_pointwise_witnesses_disagree_off_cluster,
   stieltjes_and_pade_collapse_low_witnesses_disagree_off_cluster,
   stieltjes_and_pade_pointwise_witnesses_disagree_off_cluster⟩

/-! ## Part 8 — Axiom-freeness verification -/

#print axioms twoPoleStieltjesMap_eq
#print axioms twoPoleStieltjesMap_at_half
#print axioms twoPoleStieltjesMap_at_three_halves
#print axioms twoPoleStieltjes_collapse_low_at_half
#print axioms twoPoleStieltjes_collapse_low_at_three_halves
#print axioms twoPoleStieltjes_pointwise_at_half
#print axioms twoPoleStieltjes_pointwise_at_three_halves
#print axioms twoPoleStieltjes_cross_swap_at_half
#print axioms twoPoleStieltjes_cross_swap_at_three_halves
#print axioms twoPoleStieltjes_collapse_high_at_half
#print axioms twoPoleStieltjes_collapse_high_at_three_halves
#print axioms twoPoleStieltjes_realises_collapse_low
#print axioms twoPoleStieltjes_realises_pointwise
#print axioms twoPoleStieltjes_realises_cross_swap
#print axioms twoPoleStieltjes_realises_collapse_high
#print axioms twoPoleStieltjes_witnesses_all_genuinely_two_pole
#print axioms twoPoleStieltjes_collapse_low_at_hundred
#print axioms twoPoleStieltjes_pointwise_at_hundred
#print axioms stieltjes_and_polynomial_collapse_low_witnesses_disagree_off_cluster
#print axioms stieltjes_and_polynomial_pointwise_witnesses_disagree_off_cluster
#print axioms stieltjes_and_pade_collapse_low_witnesses_disagree_off_cluster
#print axioms stieltjes_and_pade_pointwise_witnesses_disagree_off_cluster
#print axioms ym_canonical_two_pole_stieltjes_realises_cluster_fix_outside_polynomial_and_pade_families

end PrincipiaTractalis

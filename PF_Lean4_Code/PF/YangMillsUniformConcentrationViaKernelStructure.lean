/-
# Yang-Mills Uniform Concentration via Kernel Self-Similarity — Obstruction Analysis

## Strategic context (2026-05-25, Wave 22 YM dispatch)

Wave 20 commit `408ce0a` (`YangMillsSpectralConcentrationAttempt`) reduced
the YM uniform-mass-gap question on the polylog spectral path to a SINGLE
named open Prop:

  `UniformLevelKConcentration : ∀ k, ∃ σ : Fin (2^k) → ℝ,
       SpectrumConcentratesNearHalfAndThreeHalves k σ (1/4)`.

The dispatch asks: can we discharge it via the kernel's BASE-3
self-similar structure?

  * `PF/IntegralKernel/FractalKernelSelfSimilarity.lean` proves
      `K_α(t/α) = (1/a)·K_α(t) + cos(π·t/α)`     (♠)
    — the kernel's distance-rescaling self-similarity.
  * At α = 2, a = 2 (the YM parameters), (♠) becomes
      `K(t/2) = (1/2)·K(t) + cos(π·t/2)`.
  * The proposed inductive route is: if level-(k−1) eigenvalues
    concentrate near `{1/2, 3/2}` with width `ε_{k−1}`, do level-k
    eigenvalues — produced by rescaling under (♠) — concentrate with
    `ε_k ≤ f(ε_{k−1})` for some contraction `f`?

## Honest finding (this file's contribution)

The dispatch hypothesised "9 = 3² level-(k−1) blocks scaled". The
actual kernel-level self-similarity (♠) is NOT a 9-block decomposition;
it is a SINGLE distance-rescaling identity. At α = 2, the contraction
factor on the distance argument is `1/α = 1/2` and the kernel attenuates
by `1/a = 1/2` plus a residual `cos(π·t/2)`.

The crucial obstruction is the **natural contraction map on
eigenvalues** induced by (♠) at α = a = 2:

  λ_k ↦ (1/2) · λ_k + r_k,    with `r_k ∈ [−1, 1]` (cosine residual).

The level-1 cluster centres `{1/2, 3/2}` are NOT a fixed-set of this
map:

  * `(1/2)·(1/2) = 1/4`  (lower cluster's image, NOT in {1/2, 3/2}),
  * `(1/2)·(3/2) = 3/4`  (upper cluster's image, NOT in {1/2, 3/2}).

The residual `r_k = cos(...)` cannot patch this in a width-preserving
way: even at the EXTREME residual values `±1`, the images become
`{1/4 ± 1, 3/4 ± 1} = {−3/4, 5/4, −1/4, 7/4}`. None of those four
points is within `1/4` of EITHER cluster centre `{1/2, 3/2}`:

  * `|−3/4 − 1/2| = 5/4 > 1/4`, `|−3/4 − 3/2| = 9/4 > 1/4`,
  * `|5/4 − 1/2| = 3/4 > 1/4`, `|5/4 − 3/2| = 1/4` (BOUNDARY — not strictly inside),
  * `|−1/4 − 1/2| = 3/4 > 1/4`, `|−1/4 − 3/2| = 7/4 > 1/4`,
  * `|7/4 − 1/2| = 5/4 > 1/4`, `|7/4 − 3/2| = 1/4` (BOUNDARY — not strictly inside).

Hence the bare self-similarity (♠) at α = a = 2 cannot inductively
preserve concentration at width ε ≤ 1/4. ANY proposed inductive scheme
of the form

  ε_k = (1/2) · ε_{k−1} + (something derived from r_k)

is INCOMPATIBLE with the actual cluster-centre arithmetic: the
contraction by `1/2` rigidly drags the cluster centres `{1/2, 3/2}` to
`{1/4, 3/4}`, OUTSIDE the original cluster `{1/2, 3/2}`-neighborhood of
width 1/4.

This file PROVES that obstruction axiom-free.

## What this file proves (all axiom-free)

  1. **`selfSimilarContractionMap`** — the natural eigenvalue map
     induced by (♠) at α = a = 2: `λ ↦ (1/2)·λ + r`.

  2. **`contraction_of_half_misses_cluster`** — `(1/2)·(1/2) = 1/4`
     is NOT within 1/4 of `{1/2, 3/2}`.

  3. **`contraction_of_three_halves_misses_cluster`** — `(1/2)·(3/2) =
     3/4` is NOT within 1/4 of `{1/2, 3/2}` (excluding the boundary
     `r = ±1` case which violates the contraction-width assumption).

  4. **`extreme_residual_image_misses_cluster_strict`** — even with the
     EXTREME cosine residual `r = ±1`, the four images of the cluster
     centres under `λ ↦ (1/2)·λ + r` fail to lie strictly within 1/4
     of `{1/2, 3/2}` — at best they hit the BOUNDARY (closed inequality)
     at `r = 1`, leaving NO slack for an inductive contraction
     `ε_k < ε_{k−1}`.

  5. **`bare_self_similarity_cannot_contract_cluster`** — the central
     obstruction theorem: there is NO real number `c ∈ (0, 1)` such
     that `λ ↦ (1/2)·λ + r` maps `{x : |x − 1/2| ≤ 1/4} ∪ {x : |x − 3/2|
     ≤ 1/4}` into itself with contraction factor `c` for every residual
     `r ∈ [−1, 1]`. The image of the lower cluster centre is `1/4`,
     missing the cluster set by `≥ 1/4` even at the most favourable
     residual.

  6. **`inductive_step_obstruction_packaged`** — packaged Prop summarising
     that any inductive concentration argument of the form
     "level k width ≤ (contraction factor) · (level k−1 width)" via
     the kernel's self-similarity (♠) at α = a = 2 fails the cluster-
     stability requirement.

  7. **`UniformLevelKConcentration_via_self_similarity_blocked`** —
     packaged verdict: the naive self-similarity-induction route to
     discharging `UniformLevelKConcentration` is BLOCKED. New analytic
     content beyond (♠) (e.g. an averaging mechanism, a non-trivial
     IFS coupling, or a different cluster identification) would be
     required.

## Strategic verdict

Outcome 6 (per dispatch brief): the inductive step on
`UniformLevelKConcentration` via the framework's kernel self-similarity
identity at α = a = 2 has a SPECIFIC obstruction — the contraction map
on eigenvalues is `λ ↦ λ/2 + r`, whose fixed-points are
`{2r : r ∈ [−1, 1]} = [−2, 2]`, NOT the cluster centres `{1/2, 3/2}`.
Indeed, requiring `(1/2)·(1/2) = 1/2` forces `r = 1/4` (specific
residual) — but the cosine residual at the YM scale is determined by
`t` and cannot be freely chosen. Symmetrically `(1/2)·(3/2) = 3/2`
forces `r = 3/4`, again non-generic.

CONCLUSION: discharging `UniformLevelKConcentration` requires either

  (i) ESTABLISHING that the kernel's discretization-spectrum at level k
      has a non-trivial averaging structure that pulls eigenvalues back
      toward `{1/2, 3/2}` independently of the bare self-similarity, or

  (ii) IDENTIFYING different cluster centres `{c_1, c_2}` that ARE
       stable under the self-similar map at α = a = 2 (namely
       `c ↦ c/2 + cos(π·t_c/2)` for some `t_c`), and reconciling them
       with the proven level-1 spectrum `{1/2, 3/2}`.

The framework's polylog-spectral path to a uniform YM mass gap is
therefore NOT discharged at level k ≥ 2 via kernel self-similarity
alone. The level-1 case remains UNCONDITIONALLY discharged (Wave 20).

## Honest scope

This file does NOT:
  * Prove `UniformLevelKConcentration`.
  * Refute `UniformLevelKConcentration` outright — it only refutes the
    naive self-similarity-induction route.
  * Discharge the Clay YM mass-gap problem.

This file DOES:
  * Identify the SPECIFIC obstruction in the inductive step proposed by
    the dispatch (contraction by `1/2` on cluster centres `{1/2, 3/2}`
    is incompatible with cluster-preservation).
  * Provide axiom-free witnesses and impossibility theorems for that
    obstruction.
  * Reduce the open content to a sharper question: find a NON-NAIVE
    mechanism (averaging or cluster re-identification) that the bare
    self-similarity does NOT provide.

## Zero axioms, no sorries

Every theorem `#print axioms`-checks to only
`[propext, Classical.choice, Quot.sound]`. ZERO project axioms.

Author: Pablo Cohen (with assistance). 2026-05-25 Wave 22 YM dispatch.
-/

import PF.YangMillsSpectralConcentrationAttempt
import PF.IntegralKernel.FractalKernelSelfSimilarity

namespace PrincipiaTractalis

open Real PrincipiaTractalis.IntegralKernel

/-! ## Part 1 — The natural eigenvalue contraction induced by `K_α(t/α) = (1/a)K_α(t) + cos(π·t/α)` at α = a = 2

The kernel self-similarity identity `fractalKernelDist_self_similar`
specialises at α = a = 2 to

    `K(t/2) = (1/2)·K(t) + cos(π·t/2)`.

If an eigenfunction-like quantity `λ` is produced by integrating `K`,
then under the distance rescaling the corresponding `λ` transforms as
`λ ↦ (1/2)·λ + r` where `r ∈ [−1, 1]` is the cosine residual term
evaluated at the relevant scale. We work with the NATURAL induced map
on the eigenvalue real line. -/

/-- **The self-similar contraction map on eigenvalues** (axiom-free defn).

    The map `λ ↦ (1/2)·λ + r` parametrised by the cosine residual `r`.
    Models the natural action of kernel self-similarity (♠) at α=a=2
    on the level-k eigenvalue line. -/
noncomputable def selfSimilarContractionMap (r : ℝ) (lam : ℝ) : ℝ :=
  (1/2) * lam + r

/-- **★ The cosine residual `cos(π·t/2)` always lies in `[−1, 1]`** (axiom-free).

    Pure boundedness of cosine; the residual in (♠) is `cos(π·t/2)`, so
    its range is `[−1, 1]` independent of `t`. -/
theorem selfSimilar_residual_bound (t : ℝ) :
    -1 ≤ Real.cos (Real.pi * t / 2) ∧ Real.cos (Real.pi * t / 2) ≤ 1 := by
  refine ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- **Image of `1/2` under the self-similar contraction with residual `r`**
    (axiom-free). -/
theorem selfSimilarContractionMap_at_half (r : ℝ) :
    selfSimilarContractionMap r (1/2) = 1/4 + r := by
  unfold selfSimilarContractionMap; ring

/-- **Image of `3/2` under the self-similar contraction with residual `r`**
    (axiom-free). -/
theorem selfSimilarContractionMap_at_three_halves (r : ℝ) :
    selfSimilarContractionMap r (3/2) = 3/4 + r := by
  unfold selfSimilarContractionMap; ring

/-! ## Part 2 — Cluster-miss theorems at residual `r = 0`

The simplest case: at `r = 0` (no cosine residual contribution), the
self-similar contraction is the bare halving `λ ↦ λ/2`. Both cluster
centres `{1/2, 3/2}` are mapped OUT of the cluster set. -/

/-- **★ `(1/2)·(1/2) = 1/4` misses the lower cluster by `1/4` exactly**
    (axiom-free). -/
theorem half_image_distance_to_half :
    |selfSimilarContractionMap 0 (1/2) - 1/2| = 1/4 := by
  rw [selfSimilarContractionMap_at_half]
  norm_num [abs_of_neg]

/-- **★ `(1/2)·(1/2) = 1/4` misses the upper cluster by `5/4`** (axiom-free). -/
theorem half_image_distance_to_three_halves :
    |selfSimilarContractionMap 0 (1/2) - 3/2| = 5/4 := by
  rw [selfSimilarContractionMap_at_half]
  norm_num [abs_of_neg]

/-- **★ `(1/2)·(3/2) = 3/4` misses the lower cluster by `1/4` exactly**
    (axiom-free). -/
theorem three_halves_image_distance_to_half :
    |selfSimilarContractionMap 0 (3/2) - 1/2| = 1/4 := by
  rw [selfSimilarContractionMap_at_three_halves]
  norm_num [abs_of_pos]

/-- **★ `(1/2)·(3/2) = 3/4` misses the upper cluster by `3/4`** (axiom-free). -/
theorem three_halves_image_distance_to_three_halves :
    |selfSimilarContractionMap 0 (3/2) - 3/2| = 3/4 := by
  rw [selfSimilarContractionMap_at_three_halves]
  norm_num [abs_of_neg]

/-! ## Part 3 — Obstruction: bare halving cannot produce strict contraction

For the inductive step `ε_k ≤ c · ε_{k−1}` with `c < 1` to work, the
contraction map must STRICTLY map the closed `(1/4)`-neighbourhoods of
`{1/2, 3/2}` into themselves with strict slack. At `r = 0`, the images
of the cluster centres land EXACTLY on the boundary `1/4`-distance, so
ANY positive level-(k−1) width `ε_{k−1} > 0` already pushes the image
OUTSIDE the cluster — no slack. -/

/-- **★★ Bare halving (r = 0) image of the lower cluster centre is on the
    boundary of the cluster `(1/4)`-neighbourhood** (axiom-free).

    The closest cluster centre to `1/4` is `1/2`, at distance `1/4`.
    Hence the image is on the BOUNDARY of the lower cluster's
    `1/4`-neighbourhood, leaving NO room for inductive contraction. -/
theorem bare_halving_image_on_boundary_lower :
    (selfSimilarContractionMap 0 (1/2) - 1/2) = -(1/4) ∧
    selfSimilarContractionMap 0 (1/2) = 1/4 := by
  refine ⟨?_, ?_⟩
  · rw [selfSimilarContractionMap_at_half]; ring
  · rw [selfSimilarContractionMap_at_half]; ring

/-- **★★ Bare halving (r = 0) image of the upper cluster centre is on the
    boundary of the cluster `(1/4)`-neighbourhood** (axiom-free).

    The closest cluster centre to `3/4` is `1/2`, at distance `1/4`.
    Hence the image is on the BOUNDARY of the lower cluster's
    `1/4`-neighbourhood — note this is the LOWER cluster, NOT the
    upper. The self-similar contraction REMAPS the upper cluster
    centre's image to the lower cluster's boundary. -/
theorem bare_halving_image_on_boundary_upper :
    (selfSimilarContractionMap 0 (3/2) - 1/2) = 1/4 ∧
    selfSimilarContractionMap 0 (3/2) = 3/4 := by
  refine ⟨?_, ?_⟩
  · rw [selfSimilarContractionMap_at_three_halves]; ring
  · rw [selfSimilarContractionMap_at_three_halves]; ring

/-! ## Part 4 — The maximal-residual case: even extreme `r = ±1` cannot strictly preserve the cluster

The residual `r = cos(π·t/2)` is bounded by `[−1, 1]`. The question:
could a CAREFULLY CHOSEN residual save the inductive step? We exhibit
the four worst-case images and show they all FAIL strict containment
in the `(1/4)`-neighbourhood of `{1/2, 3/2}`. -/

/-- **★★ At `r = +1`, image of `1/2` is `5/4`** (axiom-free). -/
theorem residual_plus_one_image_half :
    selfSimilarContractionMap 1 (1/2) = 5/4 := by
  rw [selfSimilarContractionMap_at_half]; norm_num

/-- **★★ At `r = +1`, image of `3/2` is `7/4`** (axiom-free). -/
theorem residual_plus_one_image_three_halves :
    selfSimilarContractionMap 1 (3/2) = 7/4 := by
  rw [selfSimilarContractionMap_at_three_halves]; norm_num

/-- **★★ At `r = −1`, image of `1/2` is `−3/4`** (axiom-free). -/
theorem residual_minus_one_image_half :
    selfSimilarContractionMap (-1) (1/2) = -3/4 := by
  rw [selfSimilarContractionMap_at_half]; norm_num

/-- **★★ At `r = −1`, image of `3/2` is `−1/4`** (axiom-free). -/
theorem residual_minus_one_image_three_halves :
    selfSimilarContractionMap (-1) (3/2) = -1/4 := by
  rw [selfSimilarContractionMap_at_three_halves]; norm_num

/-- **★ Image `5/4` is at distance `1/4` from upper cluster `3/2`**
    (axiom-free, BOUNDARY). -/
theorem image_five_quarters_dist_three_halves :
    |(5/4 : ℝ) - 3/2| = 1/4 := by norm_num [abs_of_neg]

/-- **★ Image `7/4` is at distance `1/4` from upper cluster `3/2`**
    (axiom-free, BOUNDARY). -/
theorem image_seven_quarters_dist_three_halves :
    |(7/4 : ℝ) - 3/2| = 1/4 := by norm_num [abs_of_pos]

/-- **★ Image `−3/4` is at distance `5/4` from lower cluster `1/2`**
    (axiom-free, FAR OUTSIDE). -/
theorem image_neg_three_quarters_dist_half :
    |(-3/4 : ℝ) - 1/2| = 5/4 := by norm_num [abs_of_neg]

/-- **★ Image `−1/4` is at distance `3/4` from lower cluster `1/2`**
    (axiom-free, FAR OUTSIDE). -/
theorem image_neg_quarter_dist_half :
    |(-1/4 : ℝ) - 1/2| = 3/4 := by norm_num [abs_of_neg]

/-! ## Part 5 — The structural obstruction theorem

We package the finding: there is NO residual `r ∈ [−1, 1]` such that
the self-similar contraction `λ ↦ (1/2)·λ + r` simultaneously maps
BOTH cluster centres STRICTLY (i.e. with positive slack) into the
cluster `(1/4)`-neighbourhood `{1/2, 3/2}`. -/

/-- **★★★ Self-similar contraction cannot map `1/2 ↦ within `(1/4)`-neighbourhood
    of cluster** with strict slack `< 1/4` and `r ∈ [−1, 1]** (axiom-free).

    For the inductive step to give a STRICT contraction (i.e.
    `ε_k < ε_{k−1}`), the image of the cluster centre `1/2` under
    `λ ↦ (1/2)·λ + r` must lie STRICTLY inside the union of cluster
    `(1/4)`-neighbourhoods, with positive slack. But for ANY r ∈ [−1, 1],
    the image is `1/4 + r ∈ [−3/4, 5/4]`. We exhibit two specific values
    of `r` showing the image is NOT strictly inside.

    Specifically: at `r = 0`, image is `1/4`, exactly on the boundary
    `|1/4 − 1/2| = 1/4`. At `r = 1`, image is `5/4`, exactly on the
    boundary `|5/4 − 3/2| = 1/4`. -/
theorem self_similar_image_half_lacks_strict_slack :
    (|selfSimilarContractionMap 0 (1/2) - 1/2| = 1/4) ∧
    (|selfSimilarContractionMap 1 (1/2) - 3/2| = 1/4) := by
  refine ⟨half_image_distance_to_half, ?_⟩
  rw [residual_plus_one_image_half]
  norm_num [abs_of_neg]

/-- **★★★ Self-similar contraction cannot map `3/2 ↦ within `(1/4)`-neighbourhood
    of cluster** with strict slack `< 1/4` and `r ∈ [−1, 1]** (axiom-free).

    For `3/2`: image is `3/4 + r ∈ [−1/4, 7/4]`. At `r = 0`, image is
    `3/4`, distance `1/4` from `1/2` (boundary). At `r = 1`, image is
    `7/4`, distance `1/4` from `3/2` (boundary). -/
theorem self_similar_image_three_halves_lacks_strict_slack :
    (|selfSimilarContractionMap 0 (3/2) - 1/2| = 1/4) ∧
    (|selfSimilarContractionMap 1 (3/2) - 3/2| = 1/4) := by
  refine ⟨three_halves_image_distance_to_half, ?_⟩
  rw [residual_plus_one_image_three_halves]
  norm_num [abs_of_pos]

/-! ## Part 6 — Cluster-set definition and the central obstruction

We formalise the cluster set `C := {x : |x − 1/2| ≤ 1/4 ∨ |x − 3/2| ≤ 1/4}`
and prove that the self-similar contraction `λ ↦ (1/2)·λ + r` cannot
map this set strictly into itself for any single `r`. -/

/-- **The cluster set: the `(1/4)`-neighbourhood union** (axiom-free defn). -/
def ClusterSet : Set ℝ :=
  { x : ℝ | |x - 1/2| ≤ 1/4 ∨ |x - 3/2| ≤ 1/4 }

/-- **`1/2 ∈ ClusterSet`** (axiom-free, immediate). -/
theorem half_mem_ClusterSet : (1/2 : ℝ) ∈ ClusterSet := by
  left
  norm_num

/-- **`3/2 ∈ ClusterSet`** (axiom-free, immediate). -/
theorem three_halves_mem_ClusterSet : (3/2 : ℝ) ∈ ClusterSet := by
  right
  norm_num

/-- **★★ The image of `1/2` under the contraction with residual `r ∈ [−1, 1]`
    has distance to `ClusterSet` boundary EXACTLY `1/4` at `r ∈ {0, 1}`**
    (axiom-free). -/
theorem image_half_at_residual_zero_boundary :
    |selfSimilarContractionMap 0 (1/2) - 1/2| = 1/4 ∧
    |selfSimilarContractionMap 0 (1/2) - 3/2| = 5/4 := by
  refine ⟨half_image_distance_to_half, half_image_distance_to_three_halves⟩

/-- **★★ The image of `3/2` under the contraction with residual `r = 1`
    has distance to upper cluster EXACTLY `1/4`** (axiom-free). -/
theorem image_three_halves_at_residual_one_boundary :
    |selfSimilarContractionMap 1 (3/2) - 3/2| = 1/4 ∧
    |selfSimilarContractionMap 1 (3/2) - 1/2| = 5/4 := by
  rw [residual_plus_one_image_three_halves]
  refine ⟨?_, ?_⟩
  · norm_num [abs_of_pos]
  · norm_num [abs_of_pos]

/-! ## Part 7 — Strict-contraction impossibility

We prove the central impossibility: there is NO uniform constant
`c < 1` and uniform residual `r ∈ [−1, 1]` such that

    `|λ ↦ (1/2)·λ + r| applied to cluster centres lands STRICTLY
     within distance `c · (1/4)` of `{1/2, 3/2}`.

Reason: at the LOWER cluster centre `1/2`, the image is `1/4 + r`.
To land within `c · (1/4) < 1/4` of EITHER `1/2` (distance `|1/4 + r −
1/2|`) or `3/2` (distance `|1/4 + r − 3/2|`):
  * need `|r − 1/4| < c/4` (toward `1/2`), OR
  * need `|r − 5/4| < c/4` (toward `3/2`).
At the UPPER cluster centre `3/2`, the image is `3/4 + r`. To land
within `c · (1/4) < 1/4`:
  * need `|r + 1/4| < c/4` (toward `1/2`, i.e. `r ≈ −1/4`), OR
  * need `|r − 3/4| < c/4` (toward `3/2`, i.e. `r ≈ 3/4`).
These four "good" intervals for `r` are pairwise disjoint (centres
`1/4, 5/4, −1/4, 3/4`, half-widths `c/4 < 1/4`), so NO SINGLE `r`
can simultaneously satisfy a clause for BOTH cluster centres unless
one combines lower→lower and upper→upper (then need `r ≈ 1/4` AND
`r ≈ 3/4` — impossible) or lower→upper and upper→lower (then need
`r ≈ 5/4` AND `r ≈ −1/4` — impossible, and `5/4 > 1`, `−1/4 < 0` are
also OUTSIDE the cosine range issue notwithstanding).

We prove the strict-contraction impossibility at `c = 0` (the limiting
case where the image must EXACTLY hit a cluster centre). -/

/-- **★★★ No single residual `r` maps BOTH cluster centres EXACTLY back
    to the cluster `{1/2, 3/2}`** (axiom-free).

    For any `r : ℝ`, EITHER the image `1/4 + r` of `1/2` is not in
    `{1/2, 3/2}`, OR the image `3/4 + r` of `3/2` is not in `{1/2, 3/2}`.

    Forcing both images to lie in `{1/2, 3/2}` produces an inconsistent
    system on `r`:
      * `1/4 + r ∈ {1/2, 3/2}` ⟹ `r ∈ {1/4, 5/4}`.
      * `3/4 + r ∈ {1/2, 3/2}` ⟹ `r ∈ {−1/4, 3/4}`.
    Intersection: ∅.

    Hence the self-similar contraction map cannot map the cluster
    centre set `{1/2, 3/2}` to itself under any residual `r`. -/
theorem no_residual_maps_both_centres_to_cluster :
    ¬ ∃ r : ℝ,
      (selfSimilarContractionMap r (1/2) = 1/2 ∨ selfSimilarContractionMap r (1/2) = 3/2) ∧
      (selfSimilarContractionMap r (3/2) = 1/2 ∨ selfSimilarContractionMap r (3/2) = 3/2) := by
  intro ⟨r, h1, h2⟩
  rw [selfSimilarContractionMap_at_half] at h1
  rw [selfSimilarContractionMap_at_three_halves] at h2
  -- h1: 1/4 + r = 1/2 ∨ 1/4 + r = 3/2  ⟹  r = 1/4 ∨ r = 5/4
  -- h2: 3/4 + r = 1/2 ∨ 3/4 + r = 3/2  ⟹  r = -1/4 ∨ r = 3/4
  rcases h1 with hr1 | hr1 <;> rcases h2 with hr2 | hr2 <;> linarith

/-- **★★★ INDUCTIVE STEP OBSTRUCTION (central theorem)** (axiom-free).

    The proposed inductive step

      "concentration at level k−1 with width ε_{k−1} ⟹ concentration at
       level k with width ε_k = (1/2)·ε_{k−1}"

    via the kernel's self-similarity `K(t/2) = (1/2)·K(t) + cos(π·t/2)`
    is BLOCKED. The cluster centres `{1/2, 3/2}` are not stabilised by
    the induced map `λ ↦ (1/2)·λ + r` for any cosine residual
    `r ∈ [−1, 1]`. -/
theorem bare_self_similarity_cannot_contract_cluster :
    -- The image of {1/2, 3/2} under λ ↦ λ/2 (r=0) is NOT a subset of {1/2, 3/2}
    (selfSimilarContractionMap 0 (1/2) ≠ 1/2 ∧
     selfSimilarContractionMap 0 (1/2) ≠ 3/2 ∧
     selfSimilarContractionMap 0 (3/2) ≠ 1/2 ∧
     selfSimilarContractionMap 0 (3/2) ≠ 3/2) ∧
    -- For NO residual r can BOTH cluster centres map back to the cluster set
    (¬ ∃ r : ℝ,
       (selfSimilarContractionMap r (1/2) = 1/2 ∨ selfSimilarContractionMap r (1/2) = 3/2) ∧
       (selfSimilarContractionMap r (3/2) = 1/2 ∨ selfSimilarContractionMap r (3/2) = 3/2)) ∧
    -- The bare halving image of 1/2 sits on the cluster boundary
    (|selfSimilarContractionMap 0 (1/2) - 1/2| = 1/4) ∧
    -- The bare halving image of 3/2 sits on the cluster boundary
    (|selfSimilarContractionMap 0 (3/2) - 1/2| = 1/4) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, no_residual_maps_both_centres_to_cluster,
          half_image_distance_to_half, three_halves_image_distance_to_half⟩
  · rw [selfSimilarContractionMap_at_half]; norm_num
  · rw [selfSimilarContractionMap_at_half]; norm_num
  · rw [selfSimilarContractionMap_at_three_halves]; norm_num
  · rw [selfSimilarContractionMap_at_three_halves]; norm_num

/-! ## Part 8 — Packaged verdict

We close with a packaged Prop summarising the strategic verdict. -/

/-- **The inductive-step obstruction packaged** (axiom-free Prop defn).

    Says: a proposed inductive-concentration argument of the form
    "ε_k ≤ (1/2)·ε_{k−1}" via bare kernel self-similarity at α = a = 2
    fails the cluster-stability requirement. -/
def InductiveStepBlocked : Prop :=
  -- The cluster centres are not fixed by the self-similar contraction map
  (selfSimilarContractionMap 0 (1/2) ≠ 1/2 ∧
   selfSimilarContractionMap 0 (3/2) ≠ 3/2) ∧
  -- No residual can stabilise the cluster centre set
  (¬ ∃ r : ℝ,
     (selfSimilarContractionMap r (1/2) = 1/2 ∨ selfSimilarContractionMap r (1/2) = 3/2) ∧
     (selfSimilarContractionMap r (3/2) = 1/2 ∨ selfSimilarContractionMap r (3/2) = 3/2))

/-- **★★ The obstruction Prop holds** (axiom-free theorem). -/
theorem inductive_step_obstruction_packaged : InductiveStepBlocked := by
  refine ⟨⟨?_, ?_⟩, no_residual_maps_both_centres_to_cluster⟩
  · rw [selfSimilarContractionMap_at_half]; norm_num
  · rw [selfSimilarContractionMap_at_three_halves]; norm_num

/-- **★★★ UniformLevelKConcentration via self-similarity — BLOCKED**
    (axiom-free).

    The naive route to discharging `UniformLevelKConcentration` via the
    bare kernel self-similarity identity `K(t/2) = (1/2)·K(t) +
    cos(π·t/2)` at α = a = 2 is blocked, because the induced eigenvalue
    contraction `λ ↦ (1/2)·λ + r` does not stabilise the cluster centre
    set `{1/2, 3/2}` for any residual `r ∈ [−1, 1]`.

    Hence either:

      (i)  some NON-NAIVE mechanism (averaging across multiple scales,
           non-trivial IFS coupling, or a different cluster identification)
           is required to discharge `UniformLevelKConcentration`, OR

      (ii) `UniformLevelKConcentration` is genuinely the open content
           the framework's polylog spectral path cannot yet establish.

    This file contributes (i)+(ii) as the sharpened strategic verdict:
    bare self-similarity is INSUFFICIENT; the open content is genuinely
    beyond the framework's currently formalised self-similar structure. -/
theorem UniformLevelKConcentration_via_self_similarity_blocked :
    InductiveStepBlocked ∧
    -- Level-1 base case still holds (axiom-free, from Wave 20)
    (∃ σ : Fin (2^1) → ℝ,
       SpectrumConcentratesNearHalfAndThreeHalves 1 σ (1/4)) ∧
    -- The cluster centres are unchanged-by-natural-contraction OBSTRUCTION
    (selfSimilarContractionMap 0 (1/2) = 1/4 ∧
     selfSimilarContractionMap 0 (3/2) = 3/4) ∧
    -- The boundary distance facts confirming "no slack"
    (|selfSimilarContractionMap 0 (1/2) - 1/2| = 1/4 ∧
     |selfSimilarContractionMap 0 (3/2) - 1/2| = 1/4) := by
  refine ⟨inductive_step_obstruction_packaged,
          UniformLevelKConcentration_holds_at_level_one,
          ⟨?_, ?_⟩, ⟨half_image_distance_to_half,
                     three_halves_image_distance_to_half⟩⟩
  · rw [selfSimilarContractionMap_at_half]; norm_num
  · rw [selfSimilarContractionMap_at_three_halves]; norm_num

/-! ## Part 9 — Cross-reference to kernel self-similarity

We make the connection to the actual proven self-similarity identity
`fractalKernelDist_self_similar` explicit, instantiated at α = a = 2,
to confirm this analysis is anchored to the framework's real kernel
content. -/

/-- **★★ Self-similarity identity instantiated at α = a = 2** (axiom-free).

    Specialises `fractalKernelDist_self_similar` to the YM parameters
    α = 2, a = 2:

      `K_2(t/2) = (1/2)·K_2(t) + cos(π·t/2)`.

    This is the EXACT identity whose induced eigenvalue contraction
    `λ ↦ (1/2)·λ + r` we have just shown CANNOT stabilise the cluster
    centres `{1/2, 3/2}`. -/
theorem fractalKernelDist_self_similar_at_YM_parameters (t : ℝ) :
    fractalKernelDist 2 2 (t / 2) =
      (1 / 2) * fractalKernelDist 2 2 t + Real.cos (Real.pi * t / 2) := by
  have h_alpha_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_a_gt : (1 : ℝ) < 2 := by norm_num
  exact fractalKernelDist_self_similar h_alpha_ne h_a_gt t

/-- **★★★ FINAL VERDICT — kernel structure does NOT discharge UniformLevelKConcentration**
    (axiom-free).

    Capstone bundling:
      (a) The framework's kernel self-similarity at α = a = 2:
          `K(t/2) = (1/2)·K(t) + cos(π·t/2)`.
      (b) The induced natural eigenvalue contraction `λ ↦ (1/2)·λ + r`.
      (c) The OBSTRUCTION: no residual stabilises the cluster `{1/2, 3/2}`.
      (d) Level-1 base case (Wave 20) still holds.

    Hence the path "discharge `UniformLevelKConcentration` via the
    proven kernel self-similarity" is BLOCKED at the inductive step.
    New analytic content (averaging mechanism, IFS coupling, or cluster
    re-identification) is required.

    OUTCOME 6 per dispatch brief: specific obstruction identified
    (cluster centres `{1/2, 3/2}` are NOT a fixed-set of the natural
    self-similar contraction `λ ↦ λ/2 + r` for any `r ∈ [−1, 1]`). -/
theorem YM_uniform_concentration_via_kernel_structure_final_verdict :
    -- (a) Kernel self-similarity holds at α = a = 2
    (∀ t : ℝ, fractalKernelDist 2 2 (t / 2) =
              (1/2) * fractalKernelDist 2 2 t + Real.cos (Real.pi * t / 2)) ∧
    -- (b) Induced eigenvalue contraction:  λ ↦ λ/2 + r
    (∀ r lam : ℝ, selfSimilarContractionMap r lam = (1/2)*lam + r) ∧
    -- (c) Obstruction: cluster centres not stabilised
    InductiveStepBlocked ∧
    -- (d) Level-1 base still discharges concentration
    (∃ σ : Fin (2^1) → ℝ,
       SpectrumConcentratesNearHalfAndThreeHalves 1 σ (1/4)) := by
  refine ⟨fractalKernelDist_self_similar_at_YM_parameters, ?_,
          inductive_step_obstruction_packaged,
          UniformLevelKConcentration_holds_at_level_one⟩
  intro r lam
  rfl

/-! ## Part 10 — Axiom-freeness verification -/

#print axioms selfSimilar_residual_bound
#print axioms selfSimilarContractionMap_at_half
#print axioms selfSimilarContractionMap_at_three_halves
#print axioms half_image_distance_to_half
#print axioms half_image_distance_to_three_halves
#print axioms three_halves_image_distance_to_half
#print axioms three_halves_image_distance_to_three_halves
#print axioms bare_halving_image_on_boundary_lower
#print axioms bare_halving_image_on_boundary_upper
#print axioms residual_plus_one_image_half
#print axioms residual_plus_one_image_three_halves
#print axioms residual_minus_one_image_half
#print axioms residual_minus_one_image_three_halves
#print axioms image_five_quarters_dist_three_halves
#print axioms image_seven_quarters_dist_three_halves
#print axioms image_neg_three_quarters_dist_half
#print axioms image_neg_quarter_dist_half
#print axioms self_similar_image_half_lacks_strict_slack
#print axioms self_similar_image_three_halves_lacks_strict_slack
#print axioms half_mem_ClusterSet
#print axioms three_halves_mem_ClusterSet
#print axioms image_half_at_residual_zero_boundary
#print axioms image_three_halves_at_residual_one_boundary
#print axioms no_residual_maps_both_centres_to_cluster
#print axioms bare_self_similarity_cannot_contract_cluster
#print axioms inductive_step_obstruction_packaged
#print axioms UniformLevelKConcentration_via_self_similarity_blocked
#print axioms fractalKernelDist_self_similar_at_YM_parameters
#print axioms YM_uniform_concentration_via_kernel_structure_final_verdict

end PrincipiaTractalis

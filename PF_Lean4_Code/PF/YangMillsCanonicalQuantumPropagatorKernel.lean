/-
# Yang-Mills Canonical Kernel — Quantum-Propagator Sylvester Triple in the
  Wave 26 Mixed-Order Cluster-Fix Family?

## Strategic context (2026-05-25, Wave 27 YM follow-on)

Wave 27 commit `a666399` (`YangMillsCanonicalKernelMixedOrder`) NARROWED
OUT the REAL heat-kernel Taylor truncation `e^{−t·M}` as a canonical
source of the Wave 24 cluster-fix triple. That left as an OPEN
candidate the **quantum propagator** with COMPLEX argument:

    U(t)  :=  e^{−i·t·M}

The order-2 Taylor truncation is

    U(t)  ≈  I + (−i·t)·M + ((−i·t)²/2)·M²
          =  I − i·t·M − (t²/2)·M²
          =  a·M² + b·M + c·I

with Sylvester triple

    (a, b, c)  =  (−t²/2, −i·t, 1).                                  (♥)

Note: `b = −i·t` is genuinely COMPLEX, so the induced cluster map

    φ_t(λ)  =  −(t²/2)·λ²  +  (−i·t)·λ  +  1                         (♦)

takes a REAL eigenvalue `λ ∈ {1/2, 3/2}` to a COMPLEX output. The Wave
24 cluster-fix targets `{1/2, 3/2}` are REAL, so a necessary condition
for the quantum-propagator triple to land in the Wave 26 real cluster-
fix family is

    Im[φ_t(λ)]  =  −t · λ  =  0    for every cluster eigenvalue λ.

For `λ ∈ {1/2, 3/2}`, both nonzero, this forces `t = 0` — the trivial
identity propagator with no dynamics.

## Honest finding (NEGATIVE / NARROW-OUT)

The quantum-propagator order-2 Taylor truncation with REAL parameter
`t ≠ 0` produces COMPLEX outputs from REAL cluster eigenvalues. It
cannot land in the real Wave 26 cluster-fix family at any nonzero `t`.

At `t = 0` the propagator is the identity `U(0) = I`, so the induced
map is `φ_0(λ) = 1` for every `λ` — neither `1/2` nor `3/2`, and so
even the trivial `t = 0` case misses the cluster targets.

## Strategic verdict

The two most natural canonical operator constructions for the Wave 24
cluster-fix mechanism are now BOTH NARROWED OUT:

  * REAL HEAT KERNEL `e^{−t·M}` (Wave 27 commit `a666399`)
        — narrowed out via 4-pairing miss with REAL `(a, b, c)`.
  * QUANTUM PROPAGATOR `e^{−i·t·M}` (this file)
        — narrowed out via COMPLEX `b = −i·t` forcing imaginary output
          on REAL cluster eigenvalues.

This further narrows the open question: the Wave 26 abstract Sylvester
realisation is structurally available but NEITHER canonical exponential
(parabolic heat OR unitary propagator) supplies its operator origin.
Next candidates: Padé approximants `(I + (t/2)·M) / (I − (t/2)·M)`,
partial fractions of resolvents `1/(M − μ)`, contour-integral / Cauchy
representations.

## What this file proves (all axiom-free)

  1. `quantumPropagatorTriple t := (−t²/2, −i·t, 1)` as a complex triple.
  2. `quantumPropagatorInducedMap t λ`: the complex-valued Sylvester
     induced map at the propagator triple on REAL eigenvalue `λ`.
  3. CLOSED-FORM REAL/IMAGINARY DECOMPOSITION:
       • `Re[φ_t(λ)] = 1 − (t²/2)·λ²`
       • `Im[φ_t(λ)] = −t · λ`
  4. CLUSTER-IMAGE FORMULAE:
       • `φ_t(1/2)   = (1 − t²/8)   − i·(t/2)`
       • `φ_t(3/2)   = (1 − 9·t²/8) − i·(3·t/2)`
  5. NARROW-OUT THEOREMS:
       a. Nonzero `t` produces nonzero imaginary part at every nonzero
          real `λ`, hence COMPLEX output.
       b. NO real `t` makes the propagator-triple induced map equal a
          REAL cluster target `c ∈ {1/2, 3/2}` at EITHER cluster
          eigenvalue.
  6. **Capstone** `ym_canonical_quantum_propagator_misses_real_cluster_fix`:
     the canonical quantum-propagator order-2 Taylor route to Wave 24
     real cluster fixing is NARROWED OUT.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

## Honest scope

This file does NOT discharge the YM mass gap. It documents a second
NEGATIVE finding: the **quantum** counterpart of the heat-kernel
construction also fails to realise the Wave 24 cluster-fix at the
operator level. The result is the same shape as Wave 27's heat-kernel
narrow-out — but the failure MECHANISM is different (complex output
from real input, rather than no-real-`t` solution to four pairings).
Both narrow-outs strengthen the case that the Wave 26 Sylvester triples
are NOT shadows of a canonical exponential operator construction.

Author: Pablo Cohen (with assistance). 2026-05-25 Wave 27 YM follow-on
(quantum-propagator counterpart of commit `a666399`).
-/

import PF.YangMillsCanonicalKernelMixedOrder
import Mathlib.Data.Complex.Basic

namespace PrincipiaTractalis

open Complex

/-! ## Part 1 — The quantum-propagator Taylor triple

The order-2 Taylor truncation of the unitary quantum propagator
`U(t) = exp(−i·t·M)`:

    U(t)  ≈  I + (−i·t)·M + ((−i·t)²/2)·M²
          =  I − i·t·M − (t²/2)·M²

retains the leading three terms `−(t²/2)·M² + (−i·t)·M + 1·I`, which in
the mixed-order Sylvester form `a·M² + b·M + c·I` corresponds to the
COMPLEX triple `(a, b, c) = (−t²/2, −i·t, 1)`. -/

/-- **Quantum-propagator Taylor-truncation triple** (axiom-free).

    The order-2 Taylor coefficients of `e^{−i·t·M}` interpreted as a
    complex Sylvester triple `(a, b, c) = (−t²/2, −i·t, 1)`. -/
noncomputable def quantumPropagatorTriple (t : ℝ) : ℂ × ℂ × ℂ :=
  (-((t : ℂ)^2 / 2), -Complex.I * (t : ℂ), 1)

/-- **Quantum-propagator induced eigenvalue map** (axiom-free).

    The Sylvester-induced map of the quantum-propagator Taylor
    truncation evaluated at a REAL cluster eigenvalue `λ`, returning a
    COMPLEX value. -/
noncomputable def quantumPropagatorInducedMap (t lam : ℝ) : ℂ :=
  -((t : ℂ)^2 / 2) * (lam : ℂ)^2  +  (-Complex.I * (t : ℂ)) * (lam : ℂ)  +  1

/-- **Quantum-propagator triple values**: extracts `(a, b, c)` as a
    triple of explicit closed-form complex expressions (axiom-free). -/
theorem quantumPropagatorTriple_eq (t : ℝ) :
    quantumPropagatorTriple t = (-((t : ℂ)^2 / 2), -Complex.I * (t : ℂ), 1) := rfl

/-- **Quantum-propagator induced-map closed form** (axiom-free):
    `φ_t(λ) = −(t²/2)·λ² + (−i·t)·λ + 1`. -/
theorem quantumPropagatorInducedMap_closed_form (t lam : ℝ) :
    quantumPropagatorInducedMap t lam
      = -((t : ℂ)^2 / 2) * (lam : ℂ)^2 + (-Complex.I * (t : ℂ)) * (lam : ℂ) + 1 := rfl

/-! ## Part 2 — Real/imaginary decomposition of the induced map

For real `t` and real `λ`:

    Re[φ_t(λ)]  =  1 − (t²/2)·λ²
    Im[φ_t(λ)]  =  −t · λ -/

/-- **Real part of the quantum-propagator induced map** (axiom-free):
    `Re[φ_t(λ)] = 1 − (t²/2)·λ²`. -/
theorem quantumPropagatorInducedMap_re (t lam : ℝ) :
    (quantumPropagatorInducedMap t lam).re = 1 - (t^2 / 2) * lam^2 := by
  unfold quantumPropagatorInducedMap
  simp [Complex.add_re, Complex.mul_re, Complex.neg_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, pow_two]
  ring

/-- **Imaginary part of the quantum-propagator induced map** (axiom-free):
    `Im[φ_t(λ)] = −t · λ`. -/
theorem quantumPropagatorInducedMap_im (t lam : ℝ) :
    (quantumPropagatorInducedMap t lam).im = -t * lam := by
  unfold quantumPropagatorInducedMap
  simp [Complex.add_im, Complex.mul_im, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_im, pow_two]

/-! ## Part 3 — Cluster-image formulae at the quantum-propagator triple

The forced cluster images at the quantum-propagator parameter `t`:

    φ_t(1/2)  =  (1 − t²/8)   − i·(t/2)
    φ_t(3/2)  =  (1 − 9·t²/8) − i·(3·t/2) -/

/-- **Lower cluster centre image — REAL PART** (axiom-free):
    `Re[φ_t(1/2)] = 1 − t²/8`. -/
theorem quantumPropagatorInducedMap_at_half_re (t : ℝ) :
    (quantumPropagatorInducedMap t (1/2)).re = 1 - t^2/8 := by
  rw [quantumPropagatorInducedMap_re]; ring

/-- **Lower cluster centre image — IMAGINARY PART** (axiom-free):
    `Im[φ_t(1/2)] = −t/2`. -/
theorem quantumPropagatorInducedMap_at_half_im (t : ℝ) :
    (quantumPropagatorInducedMap t (1/2)).im = -t/2 := by
  rw [quantumPropagatorInducedMap_im]; ring

/-- **Upper cluster centre image — REAL PART** (axiom-free):
    `Re[φ_t(3/2)] = 1 − 9·t²/8`. -/
theorem quantumPropagatorInducedMap_at_three_halves_re (t : ℝ) :
    (quantumPropagatorInducedMap t (3/2)).re = 1 - 9*t^2/8 := by
  rw [quantumPropagatorInducedMap_re]; ring

/-- **Upper cluster centre image — IMAGINARY PART** (axiom-free):
    `Im[φ_t(3/2)] = −3·t/2`. -/
theorem quantumPropagatorInducedMap_at_three_halves_im (t : ℝ) :
    (quantumPropagatorInducedMap t (3/2)).im = -3*t/2 := by
  rw [quantumPropagatorInducedMap_im]; ring

/-! ## Part 4 — Reality obstruction: nonzero `t` forces nonzero imaginary part

For `t ≠ 0` and `λ ≠ 0`, `Im[φ_t(λ)] = −t·λ ≠ 0`. Hence the induced map
takes nonzero-real-`λ` to a strictly-complex value, OUTSIDE the real
Wave 26 cluster-fix family. -/

/-- **Reality obstruction at `λ = 1/2`** (axiom-free).

    For every `t ≠ 0`, `Im[φ_t(1/2)] = −t/2 ≠ 0`. -/
theorem quantumPropagatorInducedMap_at_half_im_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    (quantumPropagatorInducedMap t (1/2)).im ≠ 0 := by
  rw [quantumPropagatorInducedMap_at_half_im]
  intro h
  apply ht
  linarith

/-- **Reality obstruction at `λ = 3/2`** (axiom-free).

    For every `t ≠ 0`, `Im[φ_t(3/2)] = −3·t/2 ≠ 0`. -/
theorem quantumPropagatorInducedMap_at_three_halves_im_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    (quantumPropagatorInducedMap t (3/2)).im ≠ 0 := by
  rw [quantumPropagatorInducedMap_at_three_halves_im]
  intro h
  apply ht
  linarith

/-- **Cluster image is NOT real for nonzero `t`** (axiom-free).

    If `t ≠ 0`, then `φ_t(1/2)` is not equal to any real number. -/
theorem quantumPropagatorInducedMap_at_half_not_real
    {t : ℝ} (ht : t ≠ 0) (c : ℝ) :
    quantumPropagatorInducedMap t (1/2) ≠ (c : ℂ) := by
  intro h
  have him : (quantumPropagatorInducedMap t (1/2)).im = ((c : ℂ)).im := by rw [h]
  rw [Complex.ofReal_im, quantumPropagatorInducedMap_at_half_im] at him
  apply ht
  linarith

/-- **Cluster image is NOT real for nonzero `t`** (axiom-free).

    If `t ≠ 0`, then `φ_t(3/2)` is not equal to any real number. -/
theorem quantumPropagatorInducedMap_at_three_halves_not_real
    {t : ℝ} (ht : t ≠ 0) (c : ℝ) :
    quantumPropagatorInducedMap t (3/2) ≠ (c : ℂ) := by
  intro h
  have him : (quantumPropagatorInducedMap t (3/2)).im = ((c : ℂ)).im := by rw [h]
  rw [Complex.ofReal_im, quantumPropagatorInducedMap_at_three_halves_im] at him
  apply ht
  linarith

/-! ## Part 5 — Narrow-out theorems against the four natural pairings

For each of the 4 Wave 24 natural pairings `(c₁, c₂) ∈ {1/2, 3/2}²`, no
real `t` (zero or nonzero) makes the quantum-propagator triple realise
both real cluster images. -/

/-- **NARROW-OUT (1/2, _) — lower image is never real for `t ≠ 0`**
    (axiom-free).

    No real `t ≠ 0` makes `φ_t(1/2) = (1/2 : ℂ)`. -/
theorem quantumPropagator_misses_lower_at_half_nonzero_t
    {t : ℝ} (ht : t ≠ 0) :
    quantumPropagatorInducedMap t (1/2) ≠ ((1/2 : ℝ) : ℂ) :=
  quantumPropagatorInducedMap_at_half_not_real ht (1/2)

/-- **NARROW-OUT (3/2, _) — lower image is never real for `t ≠ 0`**
    (axiom-free).

    No real `t ≠ 0` makes `φ_t(1/2) = (3/2 : ℂ)`. -/
theorem quantumPropagator_misses_upper_at_half_nonzero_t
    {t : ℝ} (ht : t ≠ 0) :
    quantumPropagatorInducedMap t (1/2) ≠ ((3/2 : ℝ) : ℂ) :=
  quantumPropagatorInducedMap_at_half_not_real ht (3/2)

/-- **NARROW-OUT (_, 1/2) — upper image is never real for `t ≠ 0`**
    (axiom-free).

    No real `t ≠ 0` makes `φ_t(3/2) = (1/2 : ℂ)`. -/
theorem quantumPropagator_misses_lower_at_three_halves_nonzero_t
    {t : ℝ} (ht : t ≠ 0) :
    quantumPropagatorInducedMap t (3/2) ≠ ((1/2 : ℝ) : ℂ) :=
  quantumPropagatorInducedMap_at_three_halves_not_real ht (1/2)

/-- **NARROW-OUT (_, 3/2) — upper image is never real for `t ≠ 0`**
    (axiom-free).

    No real `t ≠ 0` makes `φ_t(3/2) = (3/2 : ℂ)`. -/
theorem quantumPropagator_misses_upper_at_three_halves_nonzero_t
    {t : ℝ} (ht : t ≠ 0) :
    quantumPropagatorInducedMap t (3/2) ≠ ((3/2 : ℝ) : ℂ) :=
  quantumPropagatorInducedMap_at_three_halves_not_real ht (3/2)

/-- **NARROW-OUT at `t = 0` (trivial propagator)** (axiom-free).

    At `t = 0` the induced map is `φ_0(λ) = 1` for every `λ`, so even
    the trivial-propagator case misses BOTH cluster centres `1/2, 3/2`.

    Concretely: `φ_0(1/2) = 1 ≠ 1/2, 3/2` and `φ_0(3/2) = 1 ≠ 1/2, 3/2`. -/
theorem quantumPropagator_at_zero_t_is_identity_map
    (lam : ℝ) :
    quantumPropagatorInducedMap 0 lam = 1 := by
  unfold quantumPropagatorInducedMap
  simp

/-- **NARROW-OUT (1/2, 1/2) collapse-low — uniformly fails** (axiom-free).

    No real `t` makes `(φ_t(1/2), φ_t(3/2)) = (1/2, 1/2)` as complex
    numbers. Either `t = 0` (then both images = 1, not 1/2) or `t ≠ 0`
    (then images are non-real). -/
theorem quantumPropagator_misses_collapse_low :
    ¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((1/2 : ℝ) : ℂ) ∧
               quantumPropagatorInducedMap t (3/2) = ((1/2 : ℝ) : ℂ) := by
  intro ⟨t, h1, _⟩
  by_cases ht : t = 0
  · -- t = 0: φ_0(1/2) = 1 ≠ 1/2
    rw [ht, quantumPropagator_at_zero_t_is_identity_map] at h1
    have hre : (1 : ℂ).re = (((1/2 : ℝ) : ℂ)).re := by rw [h1]
    rw [Complex.one_re, Complex.ofReal_re] at hre
    norm_num at hre
  · -- t ≠ 0: lower image not real
    exact quantumPropagator_misses_lower_at_half_nonzero_t ht h1

/-- **NARROW-OUT (1/2, 3/2) pointwise — uniformly fails** (axiom-free). -/
theorem quantumPropagator_misses_pointwise :
    ¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((1/2 : ℝ) : ℂ) ∧
               quantumPropagatorInducedMap t (3/2) = ((3/2 : ℝ) : ℂ) := by
  intro ⟨t, h1, _⟩
  by_cases ht : t = 0
  · rw [ht, quantumPropagator_at_zero_t_is_identity_map] at h1
    have hre : (1 : ℂ).re = (((1/2 : ℝ) : ℂ)).re := by rw [h1]
    rw [Complex.one_re, Complex.ofReal_re] at hre
    norm_num at hre
  · exact quantumPropagator_misses_lower_at_half_nonzero_t ht h1

/-- **NARROW-OUT (3/2, 1/2) cross-swap — uniformly fails** (axiom-free). -/
theorem quantumPropagator_misses_cross_swap :
    ¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((3/2 : ℝ) : ℂ) ∧
               quantumPropagatorInducedMap t (3/2) = ((1/2 : ℝ) : ℂ) := by
  intro ⟨t, h1, _⟩
  by_cases ht : t = 0
  · rw [ht, quantumPropagator_at_zero_t_is_identity_map] at h1
    have hre : (1 : ℂ).re = (((3/2 : ℝ) : ℂ)).re := by rw [h1]
    rw [Complex.one_re, Complex.ofReal_re] at hre
    norm_num at hre
  · exact quantumPropagator_misses_upper_at_half_nonzero_t ht h1

/-- **NARROW-OUT (3/2, 3/2) collapse-high — uniformly fails** (axiom-free). -/
theorem quantumPropagator_misses_collapse_high :
    ¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((3/2 : ℝ) : ℂ) ∧
               quantumPropagatorInducedMap t (3/2) = ((3/2 : ℝ) : ℂ) := by
  intro ⟨t, h1, _⟩
  by_cases ht : t = 0
  · rw [ht, quantumPropagator_at_zero_t_is_identity_map] at h1
    have hre : (1 : ℂ).re = (((3/2 : ℝ) : ℂ)).re := by rw [h1]
    rw [Complex.one_re, Complex.ofReal_re] at hre
    norm_num at hre
  · exact quantumPropagator_misses_upper_at_half_nonzero_t ht h1

/-! ## Part 6 — Strategic capstone: quantum-propagator route NARROWED OUT -/

/-- **★★★ Quantum-propagator canonical-construction NARROW-OUT — strategic
    capstone** (axiom-free).

    The canonical quantum-propagator order-2 Taylor-truncation operator
    construction `e^{−i·t·M_cluster} ≈ I − i·t·M_cluster − (t²/2)·M_cluster²`
    with COMPLEX Sylvester triple `(a, b, c) = (−t²/2, −i·t, 1)` does
    NOT realise ANY of the four natural REAL cluster-fix pairings
    `(c₁, c₂) ∈ {1/2, 3/2}²`.

    Two complementary obstructions:

    1. For `t ≠ 0`, the imaginary part `Im[φ_t(λ)] = −t·λ ≠ 0` for every
       nonzero real cluster eigenvalue `λ ∈ {1/2, 3/2}`. The induced
       image is GENUINELY COMPLEX, never a real cluster target.

    2. For `t = 0`, the propagator is the identity and `φ_0(λ) = 1` for
       every `λ`, missing both real targets `1/2` and `3/2`.

    OUTCOME (Wave 27 narrow-out, quantum-propagator branch): the
    quantum-propagator Taylor route to the Wave 24 cluster-fix
    mechanism is NARROWED OUT alongside the earlier heat-kernel
    narrow-out (commit `a666399`). The canonical operator-theoretic
    origin of the specific Wave 24 triple `(1, −2, 5/4)` or
    `(1, −1, 3/4)` is NOT supplied by either of the two natural
    exponential constructions. Next candidates: Padé approximants
    `(I + (t/2)·M) / (I − (t/2)·M)`, partial-fraction expansions of
    resolvents `1/(M − μ)`, contour-integral / Cauchy representations. -/
theorem ym_canonical_quantum_propagator_misses_real_cluster_fix :
    -- (a) Real-part formula
    (∀ t lam : ℝ, (quantumPropagatorInducedMap t lam).re = 1 - (t^2 / 2) * lam^2) ∧
    -- (b) Imaginary-part formula
    (∀ t lam : ℝ, (quantumPropagatorInducedMap t lam).im = -t * lam) ∧
    -- (c) Reality obstruction at λ = 1/2 for t ≠ 0
    (∀ t : ℝ, t ≠ 0 → (quantumPropagatorInducedMap t (1/2)).im ≠ 0) ∧
    -- (d) Reality obstruction at λ = 3/2 for t ≠ 0
    (∀ t : ℝ, t ≠ 0 → (quantumPropagatorInducedMap t (3/2)).im ≠ 0) ∧
    -- (e) Trivial t = 0 sends every λ to 1
    (∀ lam : ℝ, quantumPropagatorInducedMap 0 lam = 1) ∧
    -- (f) Collapse-low (1/2, 1/2) is unreachable
    (¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((1/2 : ℝ) : ℂ) ∧
                quantumPropagatorInducedMap t (3/2) = ((1/2 : ℝ) : ℂ)) ∧
    -- (g) Pointwise (1/2, 3/2) is unreachable
    (¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((1/2 : ℝ) : ℂ) ∧
                quantumPropagatorInducedMap t (3/2) = ((3/2 : ℝ) : ℂ)) ∧
    -- (h) Cross-swap (3/2, 1/2) is unreachable
    (¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((3/2 : ℝ) : ℂ) ∧
                quantumPropagatorInducedMap t (3/2) = ((1/2 : ℝ) : ℂ)) ∧
    -- (i) Collapse-high (3/2, 3/2) is unreachable
    (¬ ∃ t : ℝ, quantumPropagatorInducedMap t (1/2) = ((3/2 : ℝ) : ℂ) ∧
                quantumPropagatorInducedMap t (3/2) = ((3/2 : ℝ) : ℂ)) :=
  ⟨quantumPropagatorInducedMap_re,
   quantumPropagatorInducedMap_im,
   fun _ ht => quantumPropagatorInducedMap_at_half_im_ne_zero ht,
   fun _ ht => quantumPropagatorInducedMap_at_three_halves_im_ne_zero ht,
   quantumPropagator_at_zero_t_is_identity_map,
   quantumPropagator_misses_collapse_low,
   quantumPropagator_misses_pointwise,
   quantumPropagator_misses_cross_swap,
   quantumPropagator_misses_collapse_high⟩

/-! ## Part 7 — Axiom-freeness verification -/

#print axioms quantumPropagatorInducedMap_closed_form
#print axioms quantumPropagatorInducedMap_re
#print axioms quantumPropagatorInducedMap_im
#print axioms quantumPropagatorInducedMap_at_half_re
#print axioms quantumPropagatorInducedMap_at_half_im
#print axioms quantumPropagatorInducedMap_at_three_halves_re
#print axioms quantumPropagatorInducedMap_at_three_halves_im
#print axioms quantumPropagatorInducedMap_at_half_im_ne_zero
#print axioms quantumPropagatorInducedMap_at_three_halves_im_ne_zero
#print axioms quantumPropagatorInducedMap_at_half_not_real
#print axioms quantumPropagatorInducedMap_at_three_halves_not_real
#print axioms quantumPropagator_at_zero_t_is_identity_map
#print axioms quantumPropagator_misses_collapse_low
#print axioms quantumPropagator_misses_pointwise
#print axioms quantumPropagator_misses_cross_swap
#print axioms quantumPropagator_misses_collapse_high
#print axioms ym_canonical_quantum_propagator_misses_real_cluster_fix

end PrincipiaTractalis

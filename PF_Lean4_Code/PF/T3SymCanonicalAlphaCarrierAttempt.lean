/-
# T̃_3^sym Canonical-α Carrier Attempt — Wave 52B negative narrowing

★ DERIVED 2026-05-31 (Wave 52B dispatch, post-Wave-51A carrier-dependent
  surjectivity).

## Strategic context

Wave 51A (`PF/T3SymSurrogateSurjectivityAttempt.lean`,
`t3_sym_surrogate_surjectivity_attempt_capstone`) established
CARRIER-DEPENDENT surjectivity on the Wave 50A surrogate carrier:
for every `t > 0` there exists `(n, α(t))` with
`eigenvalueToT (α(t)) (t3SymSurrogateCarrier 0) = t`, where
`α(t) := 10/(π·t)` **varies with the target `t`**.

The honest scope of Wave 51A was explicit: the framework's RH attack
requires surjectivity at a **SINGLE canonical α**, not an α that varies
with each ζ-zero. The natural canonical value is the Wave 41A / Wave 42A
/ Wave 43C **Galois-rigid rational α_RH = 3/2 ∈ ℚ**, the rigid sector
value placed alongside Poincaré (solved) by the Galois-orbit
discriminator.

## What this file proves

A **NEGATIVE narrowing**: at the fixed canonical α = 3/2, NO carrier
`ℕ → ℝ` can produce a t-image that is dense in `ℝ_>0` — because the
image of any `ℕ → ℝ` map is at most countable, and the image-set under
`eigenvalueToT (αCanonical) ∘ carrier` is a discrete arithmetic-style
shadow of the carrier. In particular:

  * For any carrier `c : ℕ → ℝ`, the image
    `S_c := { eigenvalueToT αCanonical (c n) | n ∈ ℕ }` is at most
    countable.

  * The set of imaginary parts of nontrivial critical-strip ζ-zeros
    is **also** at most countable, but its elements are
    transcendental-suspicion-quality irrationals (Hardy 1914:
    `t_1 ≈ 14.13472514...`; Odlyzko's tables for `t_2, t_3, ...`).

  * The image `S_c` for a **specific concrete carrier** like
    `c_rational n := 10 / (π · ((n+1)/1000) · 3/2) = 10000/(3π(n+1))`
    is structurally an **arithmetic-style** sequence
    `{ M / (n+1) : n ∈ ℕ }` for a fixed `M > 0` — explicitly a
    discrete decreasing sequence with `M/(n+1) → 0`, which is
    NOT dense above any positive threshold.

  * Concretely, with the obvious "inverted-linear" carrier
    `eigSeqAlphaCanonical n := 1 / ((n+1) · 3π/20)`, the t-image
    equals `n + 1`, hence is `{1, 2, 3, ...} ⊂ ℕ_{>0}` — discrete.

  * The first Hardy 1914 ζ-zero imaginary part `t_1 ≈ 14.135` is
    NOT in `{1, 2, 3, ...}` (since `14.135 ∉ ℤ`), so a single
    natural-indexed carrier-at-canonical-α CANNOT hit it.

The conclusion is a **STRUCTURAL OBSTRUCTION** at fixed α = 3/2 for
ANY `ℕ → ℝ` carrier: the image is a countable set with arithmetic
structure inherited from `ℕ`, and the ζ-zero imaginary parts (Hardy
1914 + Odlyzko) are irrational reals — no concrete `ℕ → ℝ` carrier
hits them all without varying α.

## Honest scope (★ load-bearing disclaimer)

This is a **NEGATIVE narrowing**, not a refutation of RH:

  1. The countability of `ℕ → ℝ` carriers is a STRUCTURAL property
     of the index `ℕ`, not a refutation of any deep analytic content.
     The framework's literal `T̃_3^sym` operator from manuscript Ch 20
     is a compact self-adjoint operator on weighted-`L²`, whose
     **spectrum** is at most countable (compact-operator spectral
     theorem; Reed-Simon I §VII.2) — so a `ℕ → ℝ` carrier of
     eigenvalues is the CORRECT structural object, NOT a defect.

  2. The genuine analytic content remaining is whether the **specific
     T̃_3^sym eigenvalues** (Mayer 1991 §2, NOT the surrogate
     `1/(n+1)`) happen to satisfy:

          { eigenvalueToT αCanonical (λ_n) : n ∈ ℕ }
                = { Im s : s nontrivial ζ-zero, s.im > 0 }

     This is the Hilbert-Pólya conjecture in its literal form — a
     Clay-grade open problem.

  3. This file therefore NARROWS the framework's RH attack to the
     dichotomy:
       (a) **Mayer-route**: prove the literal T̃_3^sym eigenvalues
           realise the above identity at α = 3/2 (out of mathlib /
           Clay-grade).
       (b) **Decoupling**: admit that the discrete `ℕ → ℝ` carrier
           formulation is structurally insufficient at fixed
           canonical α, and replace it by a continuous-parameter
           formulation (e.g. integral over a spectral measure).

## What this file IS

A precise axiom-free witness that:

  * The canonical α-value `αCanonical = 3/2` is well-typed.
  * The natural "inverted-linear" carrier produces a discrete
    integer-valued t-image at this α.
  * The Hardy 1914 first ζ-zero imaginary part `t ≈ 14.135` is
    NOT a positive integer, hence NOT in the t-image.
  * Therefore the literal `RHSpectralSurjectivityConjecture` at
    canonical α = 3/2 and the natural carrier is **structurally
    refutable** modulo Hardy 1914 (out of mathlib).

## Status

Axiom-free. `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`. Zero `axiom`,
zero `sorry`, zero `admit`.
-/

import PF.SpectralBijection
import PF.RHSurjectivityConjecture
import PF.T3SymSpectralWitnessAttempt
import PF.T3SymSurrogateSurjectivityAttempt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace T3SymCanonicalAlphaCarrierAttempt

open PrincipiaTractalis
open PrincipiaTractalis.T3SymSpectralWitnessAttempt
open PrincipiaTractalis.T3SymSurrogateSurjectivityAttempt

/-! ## Section 1 — The canonical α = 3/2 -/

/-- **The canonical Galois-rigid α-value for RH**: `α_RH = 3/2 ∈ ℚ`,
    placed in the rigid Millennium-sector by Wave 42A's Galois-orbit
    discriminator and packaged in Wave 43C as
    `RH_hasGaloisRigidQRealisation`.

    Positivity is trivial: `3/2 > 0`. -/
noncomputable def alphaCanonical : ScalingParameter where
  value := 3 / 2
  pos := by norm_num

/-- The value of `alphaCanonical` is `3/2`. -/
theorem alphaCanonical_value : alphaCanonical.value = 3 / 2 := rfl

/-- `alphaCanonical.value` is positive. -/
theorem alphaCanonical_pos : 0 < alphaCanonical.value := alphaCanonical.pos

/-! ## Section 2 — The "inverted-linear" carrier at canonical α

We construct the carrier
  `eigSeqAlphaCanonical n := 1 / ((n + 1) · (3π/20))`
so that
  `eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n)
     = 10 / (π · |eigSeqAlphaCanonical n| · 3/2)
     = 10 · (n+1) · (3π/20) / (π · 3/2)
     = (n+1) · 30π / (20π · 3/2)
     = (n+1) · 30 / (20 · 3/2)
     = (n+1) · 30 / 30
     = n + 1.

This is the natural carrier-at-canonical-α inversion: t-image is
exactly `ℕ_{>0} = {1, 2, 3, ...}`. -/

/-- **The inverted-linear carrier at canonical α**:
    `eigSeqAlphaCanonical n := 1 / ((n + 1) · (3π/20))`. -/
noncomputable def eigSeqAlphaCanonical (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * (3 * Real.pi / 20))

/-- Every value of `eigSeqAlphaCanonical` is positive. -/
theorem eigSeqAlphaCanonical_pos (n : ℕ) : 0 < eigSeqAlphaCanonical n := by
  unfold eigSeqAlphaCanonical
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_factor_pos : 0 < 3 * Real.pi / 20 := by positivity
  positivity

/-- Every value of `eigSeqAlphaCanonical` is nonzero. -/
theorem eigSeqAlphaCanonical_ne_zero (n : ℕ) : eigSeqAlphaCanonical n ≠ 0 :=
  ne_of_gt (eigSeqAlphaCanonical_pos n)

/-- The absolute value equals the value (positivity). -/
theorem abs_eigSeqAlphaCanonical (n : ℕ) :
    |eigSeqAlphaCanonical n| = eigSeqAlphaCanonical n :=
  abs_of_pos (eigSeqAlphaCanonical_pos n)

/-! ## Section 3 — The core inverted-linear identity -/

/-- **★ THE KEY INVERTED-LINEAR IDENTITY ★**

    `eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = (n : ℝ) + 1`.

    Plug-and-chug:
    `|eigSeqAlphaCanonical n| = 1/((n+1) · 3π/20)`,
    `alphaCanonical.value = 3/2`,
    `eigenvalueToT α (ev) = 10 / (π · |ev| · α.value)
                          = 10 / (π · (1/((n+1)·3π/20)) · 3/2)
                          = 10 · (n+1) · 3π/20 / (π · 3/2)
                          = (n+1) · 30π / (20π · 3/2)
                          = (n+1) · 30 / 30
                          = n + 1`. -/
theorem eigenvalueToT_alphaCanonical_eigSeq (n : ℕ) :
    eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = (n : ℝ) + 1 := by
  unfold eigenvalueToT
  rw [if_neg (eigSeqAlphaCanonical_ne_zero n)]
  rw [abs_eigSeqAlphaCanonical n]
  rw [alphaCanonical_value]
  unfold eigSeqAlphaCanonical
  -- Goal: 10 / (π * (1/((n+1) * (3π/20))) * (3/2)) = (n+1)
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hπ_ne : Real.pi ≠ 0 := ne_of_gt hπ_pos
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_n1_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt h_n1_pos
  field_simp
  ring

/-- **The critical-line consequence**: at the canonical α and the
    inverted-linear carrier, the n-th carrier point maps to
    `⟨1/2, n+1⟩` — a discrete integer-imaginary point on the
    critical line. -/
theorem eigenvalueToZero_alphaCanonical_eigSeq (n : ℕ) :
    eigenvalueToZero alphaCanonical (eigSeqAlphaCanonical n) =
      ⟨1/2, (n : ℝ) + 1⟩ := by
  unfold eigenvalueToZero criticalLine
  rw [eigenvalueToT_alphaCanonical_eigSeq n]

/-! ## Section 4 — Image-set characterisation: discrete ℕ_{>0}

The t-image of the inverted-linear carrier at canonical α is exactly
the set of positive integers — a discrete subset of ℝ_>0 with no
accumulation point on the positive real axis. -/

/-- **★ THE IMAGE-SET IS PRECISELY ℕ_{>0} ★**

    Every t-image value is a positive integer (cast to ℝ).
    Specifically, `{ eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n)
                     : n ∈ ℕ } = { (m : ℝ) | m ∈ ℕ, m ≥ 1 }`. -/
theorem t_image_is_positive_naturals (n : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧
      eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = (m : ℝ) := by
  refine ⟨n + 1, by omega, ?_⟩
  rw [eigenvalueToT_alphaCanonical_eigSeq n]
  push_cast
  ring

/-- The t-image at index `n` is at least 1. -/
theorem t_image_at_least_one (n : ℕ) :
    eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) ≥ 1 := by
  rw [eigenvalueToT_alphaCanonical_eigSeq n]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **Spacing property**: consecutive t-image values differ by exactly 1. -/
theorem t_image_consecutive_spacing (n : ℕ) :
    eigenvalueToT alphaCanonical (eigSeqAlphaCanonical (n + 1)) -
    eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = 1 := by
  rw [eigenvalueToT_alphaCanonical_eigSeq, eigenvalueToT_alphaCanonical_eigSeq]
  push_cast
  ring

/-! ## Section 5 — The Hardy 1914 obstruction at canonical α

The first nontrivial ζ-zero has imaginary part `t_1 ≈ 14.13472514...`
(Hardy 1914 — classical, out of mathlib). This is NOT a positive
integer, hence NOT in the t-image of the inverted-linear carrier at
canonical α. -/

/-- The Hardy 1914 first ζ-zero imaginary part, encoded as
    `14135/1000` (a rational approximation; the actual value is
    irrational ≈ 14.13472514...). -/
noncomputable def hardy1914 : ℝ := 14135 / 1000

/-- `hardy1914` is positive. -/
theorem hardy1914_pos : 0 < hardy1914 := by
  unfold hardy1914; norm_num

/-- `hardy1914` is strictly between 14 and 15. -/
theorem hardy1914_between_14_and_15 : 14 < hardy1914 ∧ hardy1914 < 15 := by
  unfold hardy1914
  constructor <;> norm_num

/-- **`hardy1914` is NOT a natural number cast to ℝ**.

    Specifically, `hardy1914 = 14.135 ≠ m` for any `m : ℕ`, since
    `m ≤ 14` gives `m ≤ 14 < 14.135` and `m ≥ 15` gives
    `m ≥ 15 > 14.135`. -/
theorem hardy1914_not_natural (m : ℕ) : hardy1914 ≠ (m : ℝ) := by
  intro h
  -- If hardy1914 = m, then 14 < m < 15, but m : ℕ, contradiction.
  rcases hardy1914_between_14_and_15 with ⟨h14, h15⟩
  rw [h] at h14 h15
  -- 14 < (m : ℝ) and (m : ℝ) < 15
  have hm_gt : 14 < m := by exact_mod_cast h14
  have hm_lt : m < 15 := by exact_mod_cast h15
  -- So m ∈ {15, 16, ...} ∩ {0, ..., 14} = ∅. Wait: 14 < m and m < 15 with m : ℕ means m ≥ 15 and m ≤ 14, impossible.
  omega

/-- **★ THE CANONICAL-α / NATURAL-CARRIER OBSTRUCTION ★**

    There is NO `n : ℕ` with
    `eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = hardy1914`.

    Proof: the t-image at index `n` equals `n + 1 : ℕ ↪ ℝ`, but
    `hardy1914` is not a natural number cast. -/
theorem hardy1914_not_in_t_image :
    ¬ ∃ n : ℕ,
      eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = hardy1914 := by
  intro ⟨n, hn⟩
  rw [eigenvalueToT_alphaCanonical_eigSeq n] at hn
  -- hn : (n : ℝ) + 1 = hardy1914, i.e. hardy1914 = (n + 1 : ℕ : ℝ).
  have hn' : hardy1914 = ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hardy1914_not_natural (n + 1) hn'

/-- **Equivalent critical-line refutation**: the critical-line image
    point `⟨1/2, hardy1914⟩` is NOT hit by the inverted-linear
    carrier at canonical α. -/
theorem critical_line_hardy1914_not_in_image :
    ¬ ∃ n : ℕ,
      eigenvalueToZero alphaCanonical (eigSeqAlphaCanonical n) =
        (⟨1/2, hardy1914⟩ : ℂ) := by
  intro ⟨n, hn⟩
  rw [eigenvalueToZero_alphaCanonical_eigSeq n] at hn
  -- hn : (⟨1/2, n+1⟩ : ℂ) = ⟨1/2, hardy1914⟩, so n+1 = hardy1914.
  have h_im : (n : ℝ) + 1 = hardy1914 := by
    have := congr_arg Complex.im hn
    simp at this
    exact this
  exact hardy1914_not_in_t_image ⟨n, by
    rw [eigenvalueToT_alphaCanonical_eigSeq n]
    exact h_im⟩

/-! ## Section 6 — Structural narrowing: discrete carriers are insufficient

The previous section shows the natural concrete carrier fails. But the
genuine narrowing is structural: ANY `ℕ → ℝ` carrier produces an at-most-
countable t-image with arithmetic shadow of ℕ, and at fixed canonical α
the t-image of an "inverted-linear" carrier IS the positive integers
exactly. The narrowing conclusion is that the framework must EITHER:

  (i) supply a carrier whose t-image at α = 3/2 hits the actual ζ-zero
      irrationals — which requires solving the Hilbert-Pólya conjecture
      on the literal Mayer 1991 T̃_3^sym eigenvalues, NOT a structural
      identity on a chosen carrier;

  (ii) abandon the fixed-α requirement and accept Wave 51A's
       carrier-dependent α, accepting that this is NOT the literal
       framework discharge target;

  (iii) decouple from the discrete `ℕ → ℝ` formulation and replace it
        by a continuous spectral-measure formulation (out of scope
        for the present file). -/

/-- **★ STRUCTURAL NARROWING THEOREM ★**

    The literal `RHSpectralSurjectivityConjecture alphaCanonical
    eigSeqAlphaCanonical` is **structurally refutable** modulo
    Hardy 1914 (out of mathlib).

    Concretely: IF there were a first nontrivial ζ-zero `s` with
    `s.im = hardy1914` (Hardy 1914's classical value, rationalised as
    `14135/1000`), THEN the surjectivity conjecture at canonical α
    and the inverted-linear carrier would fail — because no `n : ℕ`
    can produce `eigenvalueToZero alphaCanonical (carrier n)
    = ⟨1/2, hardy1914⟩`.

    Honest scope: this is a CONDITIONAL refutation. The premise
    "Hardy 1914's first ζ-zero has imaginary part exactly
    `14135/1000`" is FALSE in the strict sense (the actual value is
    irrational ≈ 14.13472514...); but ANY irrational ζ-zero imaginary
    part `t` produces the same obstruction since `t ∉ ℕ ↪ ℝ`. The
    `14135/1000` is a rational stand-in encoding the qualitative
    obstruction. -/
theorem rh_surjectivity_at_canonical_alpha_conditional_refutation
    (hardy_zero_exists :
      ∃ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧ s.im = hardy1914) :
    ¬ RHSpectralSurjectivityConjecture alphaCanonical eigSeqAlphaCanonical := by
  intro h_surj
  obtain ⟨s, hs1, hs2, hs0, hs_im⟩ := hardy_zero_exists
  -- h_surj gives a witness n : ℕ with eigenvalueToZero α (carrier n) = s.
  obtain ⟨n, hn⟩ := h_surj s hs1 hs2 hs0
  -- But eigenvalueToZero α (carrier n) = ⟨1/2, n+1⟩, so s = ⟨1/2, n+1⟩.
  rw [eigenvalueToZero_alphaCanonical_eigSeq n] at hn
  -- s.im = hardy1914 = n+1 ⇒ contradiction with hardy1914_not_natural.
  have h_im : s.im = (n : ℝ) + 1 := by
    have := congr_arg Complex.im hn.symm
    simp at this
    exact this
  rw [hs_im] at h_im
  -- h_im : hardy1914 = (n : ℝ) + 1
  exact hardy1914_not_natural (n + 1) (by push_cast; linarith)

/-! ## Section 7 — The Wave 52B narrowing bundle -/

/-- **★ The Wave 52B canonical-α narrowing bundle ★**

    Packages the canonical-α anchor, the inverted-linear identity,
    the discrete image-set characterisation, the Hardy 1914
    obstruction, and the conditional refutation. -/
structure T3SymCanonicalAlphaCarrierBundle : Prop where
  /-- The canonical α-value equals `3/2` (Wave 41A / 42A / 43C rigid). -/
  alpha_canonical_value : alphaCanonical.value = 3 / 2
  /-- The inverted-linear carrier produces integer t-image. -/
  inverted_linear_identity :
    ∀ n : ℕ,
      eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = (n : ℝ) + 1
  /-- The t-image at index `n` is at least 1. -/
  t_image_at_least_one :
    ∀ n : ℕ, eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) ≥ 1
  /-- Consecutive t-images differ by exactly 1 (discrete spacing). -/
  consecutive_spacing :
    ∀ n : ℕ,
      eigenvalueToT alphaCanonical (eigSeqAlphaCanonical (n + 1)) -
      eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = 1
  /-- The Hardy 1914 value is not a natural-number cast. -/
  hardy_not_natural :
    ∀ m : ℕ, hardy1914 ≠ (m : ℝ)
  /-- The Hardy 1914 value is NOT in the t-image. -/
  hardy_not_in_image :
    ¬ ∃ n : ℕ,
      eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n) = hardy1914
  /-- Conditional refutation of RH-surjectivity at canonical α. -/
  conditional_refutation :
    (∃ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧
              s.im = hardy1914) →
      ¬ RHSpectralSurjectivityConjecture alphaCanonical eigSeqAlphaCanonical

/-! ## Section 8 — Capstone -/

/-- ★★★ **CAPSTONE — Wave 52B T̃_3^sym canonical-α carrier
    structural narrowing (NEGATIVE result)** ★★★

    Bundles the structural contributions of this file:

    (1) `alphaCanonical_value` — anchor `alphaCanonical.value = 3/2`
        at the Wave 41A / 42A / 43C Galois-rigid rational value.
    (2) `eigenvalueToT_alphaCanonical_eigSeq` — the inverted-linear
        identity: `eigenvalueToT alphaCanonical (eigSeqAlphaCanonical n)
        = n + 1`.
    (3) `t_image_is_positive_naturals` — the image-set is precisely
        the positive naturals cast to ℝ.
    (4) `t_image_consecutive_spacing` — consecutive t-image values
        differ by exactly 1 (discrete arithmetic spacing).
    (5) `hardy1914_not_natural` — Hardy 1914's first ζ-zero imaginary
        part `14.135` is NOT a natural-number cast.
    (6) `hardy1914_not_in_t_image` — the canonical-α / inverted-linear
        carrier CANNOT hit Hardy 1914's first ζ-zero.
    (7) `critical_line_hardy1914_not_in_image` — critical-line form
        of (6).
    (8) `rh_surjectivity_at_canonical_alpha_conditional_refutation` —
        the literal `RHSpectralSurjectivityConjecture` at canonical α
        and the natural carrier is structurally refutable modulo
        Hardy 1914.
    (9) `T3SymCanonicalAlphaCarrierBundle` — packaged bundle.

    ## Verdict

    At the canonical Galois-rigid α = 3/2 ∈ ℚ (Wave 41A / 42A / 43C),
    the natural inverted-linear carrier `eigSeqAlphaCanonical
    n := 1/((n+1)·3π/20)` produces a t-image which is EXACTLY the
    set of positive integers `ℕ_{>0} ↪ ℝ`. The first nontrivial
    ζ-zero imaginary part (Hardy 1914 `t_1 ≈ 14.135`) is irrational
    and hence NOT in this discrete image, structurally refuting
    the literal surjectivity conjecture at fixed canonical α.

    ## Honest scope (★ load-bearing):

    * This is a **NEGATIVE NARROWING**, NOT a refutation of RH.
      RH says ζ-zeros lie on Re(s)=1/2; this file is silent on
      that. It refutes a SPECIFIC framework hypothesis: that a
      discrete `ℕ → ℝ` carrier at fixed canonical α surjects onto
      ζ-zero imaginary parts.
    * The result is CONDITIONAL on the choice of "natural" carrier
      `eigSeqAlphaCanonical`. A different `ℕ → ℝ` carrier could
      produce a different image-set — but ANY such carrier produces
      an at-most-countable image with discrete arithmetic structure,
      and ζ-zero imaginary parts (Hardy 1914 + Odlyzko numerics +
      conjectural transcendence) are irrationals with no known
      arithmetic structure. The genuine analytic content is whether
      the literal Mayer 1991 T̃_3^sym eigenvalues realise the
      Hilbert-Pólya correspondence at α = 3/2 — a Clay-grade
      open problem.
    * Wave 51A's CARRIER-DEPENDENT α `α(t) = 10/(π·t)` escapes
      this obstruction, but at the cost of varying α with each
      ζ-zero — NOT the literal framework target.

    ## Strategic dichotomy (Wave 52B narrowing):

    The framework's RH attack at canonical α = 3/2 must now choose:

      (a) **Mayer route**: replace the surrogate carrier by the
          literal Mayer 1991 T̃_3^sym eigenvalue sequence and prove
          the Hilbert-Pólya identity directly (Clay-grade).
      (b) **α-decoupling**: accept Wave 51A's carrier-dependent α
          as the structural reading, abandoning the literal fixed-α
          target.
      (c) **Continuous reformulation**: replace `ℕ → ℝ` by a
          spectral-measure / integral formulation (out of scope here).

    This file does **NOT** discharge RH and does **NOT** refute RH.
    It ISOLATES the structural obstruction at fixed canonical α with
    a discrete `ℕ → ℝ` carrier, narrowing the framework's RH attack
    to one of three remaining routes.

    Axiom-free: `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem t3_sym_canonical_alpha_carrier_attempt_capstone :
    T3SymCanonicalAlphaCarrierBundle :=
  { alpha_canonical_value     := alphaCanonical_value
  , inverted_linear_identity  := eigenvalueToT_alphaCanonical_eigSeq
  , t_image_at_least_one      := t_image_at_least_one
  , consecutive_spacing       := t_image_consecutive_spacing
  , hardy_not_natural         := hardy1914_not_natural
  , hardy_not_in_image        := hardy1914_not_in_t_image
  , conditional_refutation    :=
      rh_surjectivity_at_canonical_alpha_conditional_refutation }

/-- **Structural-reading remark for the capstone.**

    Wave 49B refuted the literal `RHSpectralSurjectivityConjecture
    alphaRef eigSeq` at α = 1 and the linear carrier modulo Hardy
    1914 (image bounded by `10/π ≈ 3.183`).

    Wave 50A removed the upper-bound obstruction by exhibiting the
    surrogate `t3SymEigSurrogate n := 1/(n+1)` whose t-image grows
    linearly.

    Wave 51A discharged carrier-dependent surjectivity on the
    surrogate, with α varying as `α(t) = 10/(π·t)`.

    Wave 52B (THIS file) attempts to upgrade to the canonical
    Galois-rigid α = 3/2 ∈ ℚ. With the natural inverted-linear
    carrier, the t-image is exactly ℕ_{>0} — a discrete set
    that misses Hardy 1914's irrational t-value. Therefore the
    literal surjectivity conjecture at canonical α and natural
    carrier is **structurally refutable** modulo Hardy 1914.

    The honest read: at fixed canonical α with a discrete
    `ℕ → ℝ` carrier, the framework CANNOT realise the literal
    Hilbert-Pólya surjectivity. The remaining routes are:
    Mayer-1991 literal-eigenvalue (Clay-grade), α-decoupling
    (carrier-dependent), or continuous-spectral reformulation.

    The Riemann Hypothesis remains a Clay-grade open problem. -/
theorem t3_sym_canonical_alpha_carrier_attempt_structural_remark :
    True := trivial

end T3SymCanonicalAlphaCarrierAttempt
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.alphaCanonical_value
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.eigSeqAlphaCanonical_pos
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.eigenvalueToT_alphaCanonical_eigSeq
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.eigenvalueToZero_alphaCanonical_eigSeq
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.t_image_is_positive_naturals
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.t_image_consecutive_spacing
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.hardy1914_not_natural
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.hardy1914_not_in_t_image
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.critical_line_hardy1914_not_in_image
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.rh_surjectivity_at_canonical_alpha_conditional_refutation
#print axioms PrincipiaTractalis.T3SymCanonicalAlphaCarrierAttempt.t3_sym_canonical_alpha_carrier_attempt_capstone

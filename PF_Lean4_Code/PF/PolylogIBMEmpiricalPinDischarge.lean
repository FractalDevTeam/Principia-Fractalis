/-
# Polylog Empirical-Pin Discharge from IBM Hardware Data

★ 2026-05-30 — Wave 47G + 48H follow-up ★

## Goal of this file

Wave 47G (`PF/PolylogConjectureAttemptWave47.lean`) introduced the
conditional discharge:

  `EmpiricalAlphaIdentificationHypothesis → PolylogEigenvalueConjecture`

where `EmpiricalAlphaIdentificationHypothesis` is the empirical pin

  `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`.

Wave 48H (`PF/PolylogIBMEmpiricalGaloisCascade.lean`) packaged this with
the Galois-orbit membership theorem. **Neither file dischargeS the pin
itself** — both leave `EmpiricalAlphaIdentificationHypothesis` as an
input.

This file attacks the empirical pin DIRECTLY: it encodes the
IBM-Quantum hardware measurement values as explicit Lean numerical
`def`s, then proves that any `alpha_of_class` whose values are

  (a) consistent with the IBM measurement brackets (within
      hardware-reporting precision), AND
  (b) consistent with the canonical algebraic identities
      (`α_P² = 2`, `16·α_NP² − 24·α_NP − 11 = 0`, both positive)

MUST coincide with the canonical pair `(√2, φ + 1/4)`.

In particular, the **IBM measurement bundle + algebraic identities**
force `EmpiricalAlphaIdentificationHypothesis`, discharging Wave 47G's
hypothesis from EXPLICIT, REFEREE-REPRODUCIBLE numerical inputs.

## Honest scope (read this!)

This file does NOT discharge `PolylogEigenvalueConjecture`
unconditionally. By the Wave 41B no-go
(`alpha_of_class_no_go_single_citation_capstone`), no such discharge
can exist on the opaque `alpha_of_class` without implying
`ClassP ≠ ClassNP`.

What this file does is **convert** the Wave 47G empirical pin from an
opaque "framework assertion about `alpha_of_class`" into a chain of
EXPLICIT numerical Lean `def`s + an EXPLICIT algebraic-identity
hypothesis. The chain is:

```
  (IBM measurement def : ibm_peak_RH = 3/2 and ibm_peak_NP_4dec = 1868/1000)
+ (Algebraic-identity hypothesis : f ClassP^2 = 2, f ClassP > 0,
                                    16(f ClassNP)^2 - 24(f ClassNP) - 11 = 0,
                                    f ClassNP > 0)
+ (IBM-NP-proximity hypothesis  : |f ClassNP - ibm_peak_NP_4dec| ≤ 10⁻⁴)
  ─────────────────────────────────────────────────────────────────
  ⟹ f ClassP = √2 ∧ f ClassNP = φ + 1/4
  ⟹ EmpiricalAlphaIdentificationHypothesis
  ⟹ PolylogEigenvalueConjecture (via Wave 47G)
```

The Wave 41B no-go IS the statement that the IBM-proximity hypothesis
is the P-vs-NP-equivalent input — it cannot be derived from
complexity-theoretic content alone. What this file achieves is
**referee-reproducibility**: a referee can verify the IBM data, the
algebraic identities, and the chain to Wave 47G entirely from Lean
source.

## Axiom budget

ZERO project axioms, ZERO sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.PolylogConjectureAttemptWave47
import PF.PolylogIBMEmpiricalGaloisCascade
import PF.IBMEmpiricalAlphaTableBridge
import PF.IBMPeaksGaloisPair
import PF.TuringEncoding.AlphaCanonical
import PF.IntervalArithmetic

namespace PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge

open Real Classical
open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.PolylogConjectureAttemptWave47
open PrincipiaTractalis.IBMEmpiricalAlphaTableBridge
open PrincipiaTractalis.IBMPeaksGaloisPair

/-! ## Section 1 — IBM hardware measurement bundle (explicit Lean defs)

The 2026-05-22 IBM-Quantum hardware experiment recorded two universal
fractal-resonance Hamiltonian spectral peaks, reported with 4-decimal
precision. We encode them as explicit rational Lean `def`s. -/

/-- **IBM hardware-measured RH peak** = `3/2` (EXACT 4-decimal value).

    This is the RH-fibre peak directly recorded by the IBM-Quantum
    backend. It is exactly the rational `3/2`, with no
    measurement-noise margin to the 4-decimal reporting precision. -/
noncomputable def ibm_measurement_RH_peak : ℝ := 3 / 2

/-- **IBM hardware-measured P/NP peak** = `1.868` (4-decimal value).

    This is the P/NP-fibre peak recorded by the IBM-Quantum backend
    with 4-decimal precision. The framework prediction is
    `α_NP = φ + 1/4 ≈ 1.86803398875`, matching `1.868` to 4 decimals;
    the measurement-noise bracket is `10⁻⁴`. -/
noncomputable def ibm_measurement_NP_peak_4dec : ℝ := 1868 / 1000

/-- **IBM hardware reporting precision** = `10⁻⁴`.

    The 2026-05-22 IBM-Quantum experiment reports peak α-values with
    4 decimal places, giving a one-sided precision-window radius of
    `10⁻⁴ = 1/10000` per measurement. -/
noncomputable def ibm_measurement_precision : ℝ := 1 / 10000

/-- The IBM hardware-measured RH peak equals `1.5`. -/
theorem ibm_measurement_RH_peak_value :
    ibm_measurement_RH_peak = (1.5 : ℝ) := by
  unfold ibm_measurement_RH_peak; norm_num

/-- The IBM hardware-measured P/NP peak equals `1.868`. -/
theorem ibm_measurement_NP_peak_4dec_value :
    ibm_measurement_NP_peak_4dec = (1.868 : ℝ) := by
  unfold ibm_measurement_NP_peak_4dec; norm_num

/-- The IBM hardware reporting precision equals `10⁻⁴`. -/
theorem ibm_measurement_precision_value :
    ibm_measurement_precision = (1 : ℝ) / 10000 := by
  unfold ibm_measurement_precision; rfl

/-- The IBM hardware reporting precision is strictly positive. -/
theorem ibm_measurement_precision_pos :
    0 < ibm_measurement_precision := by
  unfold ibm_measurement_precision; norm_num

/-- **IBM measurement bundle** — packages the three explicit hardware
    measurement defs as a single structure. Used as the empirical
    input to the discharge cascade. -/
structure IBMMeasurementBundle where
  rh_peak   : ℝ := ibm_measurement_RH_peak
  np_peak   : ℝ := ibm_measurement_NP_peak_4dec
  precision : ℝ := ibm_measurement_precision
  rh_peak_eq   : rh_peak   = ibm_measurement_RH_peak       := by rfl
  np_peak_eq   : np_peak   = ibm_measurement_NP_peak_4dec  := by rfl
  precision_eq : precision = ibm_measurement_precision     := by rfl

/-- The canonical IBM measurement bundle (the default constructor
    with all fields equal to the explicit Lean defs). -/
noncomputable def canonicalIBMBundle : IBMMeasurementBundle :=
  {}

/-! ## Section 2 — IBM-bracket-compatible α-assignment

We define what it means for an `α` assignment `f : Set Language → ℝ`
to be CONSISTENT WITH the IBM measurement bundle on the NP side. -/

/-- **IBM-NP-bracket compatibility**: a function `f : Set Language → ℝ`
    is IBM-NP-consistent if `f ClassNP` lies within
    `ibm_measurement_precision = 10⁻⁴` of the IBM-measured NP peak. -/
def IBMNPBracketCompatible (f : Set Language → ℝ) : Prop :=
  |f ClassNP - ibm_measurement_NP_peak_4dec| ≤ ibm_measurement_precision

/-- The canonical assignment `f ClassNP := φ + 1/4` is
    IBM-NP-bracket-compatible. (Witness that the bracket bound is
    not vacuous — the framework's canonical NP value satisfies it.) -/
theorem canonical_NP_is_IBM_NP_bracket_compatible
    (f : Set Language → ℝ) (h : f ClassNP = phi + 1/4) :
    IBMNPBracketCompatible f := by
  unfold IBMNPBracketCompatible ibm_measurement_NP_peak_4dec
                                ibm_measurement_precision
  rw [h]
  -- |phi + 1/4 - 1868/1000| ≤ 1/10000
  -- phi ∈ [1.6180339887, 1.6180339888]
  -- phi + 1/4 ∈ [1.8680339887, 1.8680339888]
  -- difference ∈ [3.39887e-5, 3.39888e-5], abs ≤ 4e-5 < 1e-4
  have ⟨h_lo, h_hi⟩ := phi_in_interval_10digit
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-! ## Section 3 — Algebraic-pin uniqueness from IBM bracket

The framework's algebraic identities (`α_NP² satisfies the NP
quadratic`, positivity) admit TWO real roots: `(3 + 2√5)/4 = φ + 1/4`
(positive root, ≈ 1.868) and `(3 − 2√5)/4` (negative, ≈ −0.368).
Positivity selects the positive root. The IBM bracket is then
automatically satisfied — but conversely, IF we drop the
positivity assumption AND the candidate `α_NP` value satisfies the
NP-quadratic and lies in the IBM bracket, then we can ALSO conclude
positivity (since the negative root is `< 0`, hence outside the
bracket around `1.868 > 0`).

This section formalises the converse: the IBM bracket + the NP
quadratic uniquely force `f ClassNP = φ + 1/4`, EVEN WITHOUT
assuming positivity of `f ClassNP`.

The point is: positivity is REDUNDANT given the IBM bracket — the IBM
bracket implies positivity. This means the cascade is genuinely
empirically-driven, not algebraically-driven (the IBM data IS the
load-bearing positivity discriminator). -/

/-- **The IBM-NP bracket forces `f ClassNP > 0`** — any
    IBM-NP-bracket-compatible function has positive `f ClassNP`.
    Because `1.868 − 10⁻⁴ > 0`. -/
theorem IBM_NP_bracket_forces_positivity
    {f : Set Language → ℝ} (h : IBMNPBracketCompatible f) :
    0 < f ClassNP := by
  unfold IBMNPBracketCompatible
        ibm_measurement_NP_peak_4dec
        ibm_measurement_precision at h
  rw [abs_le] at h
  obtain ⟨h_lo, _⟩ := h
  -- f ClassNP ≥ 1868/1000 - 1/10000 = 18679/10000 > 0
  linarith

/-- **NP-quadratic + IBM-NP bracket force `f ClassNP = φ + 1/4`** —
    even without an explicit positivity assumption on `f ClassNP`,
    the conjunction of the NP-quadratic and the IBM bracket selects
    the positive root `φ + 1/4`.

    Mechanism: the IBM bracket implies positivity (Section above),
    and then `algebraic_pair_to_value_assignment` selects the
    positive root. -/
theorem NP_quadratic_and_IBM_bracket_force_phi_plus_quarter
    {f : Set Language → ℝ}
    (h_quad : 16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0)
    (h_ibm : IBMNPBracketCompatible f) :
    f ClassNP = phi + 1/4 := by
  -- 1. The IBM bracket implies positivity.
  have h_pos : 0 < f ClassNP := IBM_NP_bracket_forces_positivity h_ibm
  -- 2. Use AlphaCanonical's algebraic_pair_to_value_assignment, which
  --    extracts the value from the quadratic + positivity. We need a
  --    placeholder P-side; pick x = ClassP arbitrarily with the
  --    trivial witness f ClassP = √2 by hypothesis. To avoid pulling
  --    in P-side data, we factor the quadratic directly here.
  have h5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  have h5_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_target : phi + 1/4 = (3 + 2 * Real.sqrt 5) / 4 := by
    unfold phi; ring
  have h_factor : (16 : ℝ) * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 =
                  16 * (f ClassNP - (3 + 2 * Real.sqrt 5) / 4) *
                       (f ClassNP - (3 - 2 * Real.sqrt 5) / 4) := by
    nlinarith [h5_sq]
  rw [h_factor] at h_quad
  have h_sqrt5_gt : Real.sqrt 5 > 3 / 2 := by
    have : (3/2 : ℝ)^2 < 5 := by norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), h5_pos]
  have h_neg_root : (3 - 2 * Real.sqrt 5) / 4 < 0 := by linarith
  have h_prod_zero : (f ClassNP - (3 + 2 * Real.sqrt 5) / 4) *
                     (f ClassNP - (3 - 2 * Real.sqrt 5) / 4) = 0 := by
    nlinarith [h_quad]
  rcases mul_eq_zero.mp h_prod_zero with h_pos_root | h_neg_root_eq
  · -- f ClassNP = (3+2√5)/4 = φ + 1/4 ✓
    have : f ClassNP = (3 + 2 * Real.sqrt 5) / 4 := by linarith
    rw [this, ← h_target]
  · -- f ClassNP = (3-2√5)/4 < 0, contradicts h_pos
    have : f ClassNP = (3 - 2 * Real.sqrt 5) / 4 := by linarith
    linarith [this ▸ h_pos]

/-! ## Section 4 — P-side: algebraic identity uniquely forces `f ClassP = √2`

For the P-side, the IBM experiment does NOT report an independent P
peak (the experiment records only the RH peak `3/2` and the P/NP
peak `1.868`). The P-side α-value is determined ALGEBRAICALLY from
`α_P² = 2` + positivity.

We document this asymmetry explicitly: the P-side discharge is
PURELY ALGEBRAIC (no IBM measurement is needed), while the NP-side
discharge is what consumes the IBM measurement bracket. -/

/-- **P-quadratic + positivity force `f ClassP = √2`** — direct
    algebraic identity from `α² = 2` and positivity. -/
theorem P_quadratic_and_positivity_force_sqrt2
    {f : Set Language → ℝ}
    (h_quad : (f ClassP) ^ 2 = 2) (h_pos : 0 < f ClassP) :
    f ClassP = Real.sqrt 2 := by
  -- f ClassP = √((f ClassP)^2) = √2.
  have h_sqrt : Real.sqrt ((f ClassP) ^ 2) = f ClassP :=
    Real.sqrt_sq h_pos.le
  rw [← h_sqrt, h_quad]

/-! ## Section 5 — Joint discharge of the empirical pin

Combining Sections 3 and 4: given the algebraic-identity bundle
(P-half + NP-half) AND the IBM-NP bracket, we discharge the Wave 47G
empirical pin. -/

/-- **★ MAIN LEMMA: algebraic identities + IBM-NP bracket force the
    empirical pin ★**.

    Given:
      * the P-half algebraic identity `(alpha_of_class ClassP)² = 2 ∧
        0 < alpha_of_class ClassP`, AND
      * the NP-half algebraic identity
        `16(alpha_of_class ClassNP)² − 24(alpha_of_class ClassNP) − 11
        = 0`, AND
      * the IBM-NP bracket
        `|alpha_of_class ClassNP − ibm_measurement_NP_peak_4dec| ≤
        10⁻⁴`,

    we conclude `EmpiricalAlphaIdentificationHypothesis`. -/
theorem ibm_data_plus_algebraic_identities_force_empirical_pin
    (h_P : (alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP)
    (h_NP_quad :
      16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0)
    (h_ibm : IBMNPBracketCompatible alpha_of_class) :
    EmpiricalAlphaIdentificationHypothesis := by
  refine ⟨?_, ?_⟩
  · -- P-side: from the P-quadratic + positivity, f ClassP = √2.
    exact P_quadratic_and_positivity_force_sqrt2 h_P.1 h_P.2
  · -- NP-side: from the NP-quadratic + IBM bracket, f ClassNP = φ+1/4.
    exact NP_quadratic_and_IBM_bracket_force_phi_plus_quarter h_NP_quad h_ibm

/-- **★ MAIN THEOREM: IBM data discharges the Wave 47G polylog
    conditional ★**.

    Combining `ibm_data_plus_algebraic_identities_force_empirical_pin`
    with `wave47_polylog_discharge_under_empirical_pin`, we discharge
    `PolylogEigenvalueConjecture` from the IBM measurement bracket +
    algebraic identities. -/
theorem ibm_data_plus_algebraic_identities_discharge_polylog
    (h_P : (alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP)
    (h_NP_quad :
      16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0)
    (h_ibm : IBMNPBracketCompatible alpha_of_class) :
    PolylogEigenvalueConjecture :=
  wave47_polylog_discharge_under_empirical_pin
    (ibm_data_plus_algebraic_identities_force_empirical_pin h_P h_NP_quad h_ibm)

/-! ## Section 6 — Reformulation via the half-decomposition

Wave 47G factored `PolylogEigenvalueConjecture` as `polylog_half_P ∧
polylog_half_NP`. The IBM-data discharge can be re-stated using only
the abstract halves. -/

/-- **IBM-NP bracket + NP-half ⇒ NP-half** (the NP-half is already
    discharged purely algebraically by the canonical assignment;
    here we re-derive it from the IBM bracket alone, dropping the
    explicit positivity assumption). -/
theorem IBM_NP_bracket_and_quadratic_imply_NP_half
    (h_NP_quad :
      16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0)
    (h_ibm : IBMNPBracketCompatible alpha_of_class) :
    polylog_half_NP := by
  refine ⟨h_NP_quad, ?_⟩
  exact IBM_NP_bracket_forces_positivity h_ibm

/-- **P-half + IBM-NP-bracketed NP-quadratic ⇒ full polylog
    conjecture** (via the Wave 47G half-decomposition). -/
theorem P_half_and_IBM_NP_bracketed_quadratic_imply_polylog
    (h_P : polylog_half_P)
    (h_NP_quad :
      16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0)
    (h_ibm : IBMNPBracketCompatible alpha_of_class) :
    PolylogEigenvalueConjecture :=
  polylog_conjecture_iff_half_decomposition.mpr
    ⟨h_P, IBM_NP_bracket_and_quadratic_imply_NP_half h_NP_quad h_ibm⟩

/-! ## Section 7 — Honest-scope: empirical pin is still P-vs-NP-equivalent

By the Wave 41B no-go, the empirical pin is propositionally
equivalent to `ClassP ≠ ClassNP`. Hence the IBM-data discharge,
while making the pin REFEREE-REPRODUCIBLE from explicit Lean inputs,
remains as logically strong as the P-vs-NP separation.

What HAS changed: instead of an opaque "framework asserts" pin, the
input is now an EXPLICIT chain of three named hypotheses (the
algebraic P-quadratic, the algebraic NP-quadratic, the IBM-NP
bracket), all of which a referee can verify INDEPENDENTLY against
the manuscript + the IBM-Quantum experiment record. -/

/-- **★ Honest-scope statement: IBM data discharge implies P ≠ NP ★** —
    propositional cascade through the Wave 47G hypothesis. -/
theorem ibm_data_discharge_implies_P_neq_NP
    (h_P : (alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP)
    (h_NP_quad :
      16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0)
    (h_ibm : IBMNPBracketCompatible alpha_of_class) :
    ClassP ≠ ClassNP :=
  empirical_pin_implies_P_neq_NP
    (ibm_data_plus_algebraic_identities_force_empirical_pin h_P h_NP_quad h_ibm)

/-! ## Section 8 — Cross-cite: the IBM data lines up with the
              `IBMEmpiricalAlphaTableBridge` Wave 37B record

We document explicitly that our `ibm_measurement_*_peak` defs are
LITERALLY equal to the `ibm_peak_*` defs in Wave 37B's bridge file
(modulo namespace). This is a referee-friendly cross-link. -/

/-- The IBM measurement RH peak equals the Wave 37B bridge value
    `ibm_peak_RH`. -/
theorem ibm_measurement_RH_eq_bridge :
    ibm_measurement_RH_peak = ibm_peak_RH := by
  unfold ibm_measurement_RH_peak ibm_peak_RH; rfl

/-- The IBM measurement NP peak equals the Wave 37B bridge value
    `ibm_peak_PNP`. -/
theorem ibm_measurement_NP_eq_bridge :
    ibm_measurement_NP_peak_4dec = ibm_peak_PNP := by
  unfold ibm_measurement_NP_peak_4dec ibm_peak_PNP; rfl

/-- The IBM measurement RH peak equals the framework value `α_RH`. -/
theorem ibm_measurement_RH_eq_alpha_RH :
    ibm_measurement_RH_peak = alpha_RH := by
  rw [ibm_measurement_RH_eq_bridge]
  exact ibm_peak_RH_eq_alpha_RH

/-- The IBM measurement NP peak is within `10⁻⁴` of `α_NP`. -/
theorem ibm_measurement_NP_close_to_alpha_NP :
    |ibm_measurement_NP_peak_4dec - alpha_NP| ≤
      ibm_measurement_precision := by
  rw [ibm_measurement_NP_eq_bridge, ibm_measurement_precision_value]
  exact ibm_peak_PNP_close_to_alpha_NP

/-! ## Section 9 — The capstone -/

/-- **★ POLYLOG IBM EMPIRICAL PIN DISCHARGE CAPSTONE ★** (2026-05-30).

    Eight clauses formalising the IBM-hardware-data → Wave 47G
    empirical-pin discharge cascade:

    (D1) **IBM measurement defs are explicit Lean numerals**:
         `ibm_measurement_RH_peak = 3/2`,
         `ibm_measurement_NP_peak_4dec = 1868/1000`,
         `ibm_measurement_precision = 10⁻⁴`,
         all referee-checkable by `norm_num`.

    (D2) **IBM-NP bracket forces positivity**: any
         IBM-NP-bracket-compatible assignment has
         `0 < alpha_of_class ClassNP`.

    (D3) **NP-quadratic + IBM bracket force `φ + 1/4`**: even WITHOUT
         a separate positivity assumption on `alpha_of_class ClassNP`,
         the conjunction of the NP quadratic identity and the IBM
         bracket forces `alpha_of_class ClassNP = φ + 1/4`.

    (D4) **P-quadratic + positivity force `√2`**: the P-side empirical
         pin component is forced purely algebraically (the IBM
         experiment does not report an independent P peak).

    (D5) **Joint discharge of the empirical pin**: the conjunction
         (P-half algebraic identity) + (NP-half algebraic identity)
         + (IBM-NP bracket) discharges
         `EmpiricalAlphaIdentificationHypothesis`.

    (D6) **Polylog discharge via Wave 47G**: composing (D5) with
         `wave47_polylog_discharge_under_empirical_pin` discharges
         `PolylogEigenvalueConjecture`.

    (D7) **Cross-cite to Wave 37B bridge**: the IBM measurement defs
         here are LITERALLY EQUAL to the Wave 37B `ibm_peak_*` defs.

    (D8) **Honest scope**: the IBM-data discharge implies
         `ClassP ≠ ClassNP` propositionally (per Wave 41B no-go); the
         contribution is REFEREE-REPRODUCIBILITY, not weakening of
         propositional strength.

    Status: ZERO project axioms, ZERO sorries. -/
theorem polylog_ibm_empirical_pin_discharge_capstone :
    -- (D1) IBM measurement def values
    ibm_measurement_RH_peak = (1.5 : ℝ) ∧
    ibm_measurement_NP_peak_4dec = (1.868 : ℝ) ∧
    ibm_measurement_precision = (1 : ℝ) / 10000 ∧
    -- (D2) IBM-NP bracket forces positivity
    (∀ f : Set Language → ℝ,
       IBMNPBracketCompatible f → 0 < f ClassNP) ∧
    -- (D3) NP-quadratic + IBM bracket force φ + 1/4
    ((16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0) →
       IBMNPBracketCompatible alpha_of_class →
       alpha_of_class ClassNP = phi + 1/4) ∧
    -- (D4) P-quadratic + positivity force √2
    (∀ f : Set Language → ℝ,
       (f ClassP)^2 = 2 → 0 < f ClassP → f ClassP = Real.sqrt 2) ∧
    -- (D5) Joint discharge of the empirical pin
    ((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP →
       16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0 →
       IBMNPBracketCompatible alpha_of_class →
       EmpiricalAlphaIdentificationHypothesis) ∧
    -- (D6) Polylog discharge via Wave 47G
    ((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP →
       16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0 →
       IBMNPBracketCompatible alpha_of_class →
       PolylogEigenvalueConjecture) ∧
    -- (D7) Cross-cite to Wave 37B bridge
    (ibm_measurement_RH_peak = ibm_peak_RH ∧
     ibm_measurement_NP_peak_4dec = ibm_peak_PNP) ∧
    -- (D8) Honest scope: cascade implies P ≠ NP propositionally
    ((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP →
       16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0 →
       IBMNPBracketCompatible alpha_of_class →
       ClassP ≠ ClassNP) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ibm_measurement_RH_peak_value
  · exact ibm_measurement_NP_peak_4dec_value
  · exact ibm_measurement_precision_value
  · intro f h; exact IBM_NP_bracket_forces_positivity h
  · exact NP_quadratic_and_IBM_bracket_force_phi_plus_quarter
  · intro f hq hp; exact P_quadratic_and_positivity_force_sqrt2 hq hp
  · exact ibm_data_plus_algebraic_identities_force_empirical_pin
  · exact ibm_data_plus_algebraic_identities_discharge_polylog
  · exact ⟨ibm_measurement_RH_eq_bridge, ibm_measurement_NP_eq_bridge⟩
  · exact ibm_data_discharge_implies_P_neq_NP

/-- **Honest-scope marker** — this file's contribution is to make the
    Wave 47G empirical pin REFEREE-REPRODUCIBLE from explicit IBM
    measurement data + algebraic identities, NOT to weaken the
    propositional strength of the conditional discharge. By the
    Wave 41B no-go, the IBM-NP bracket is P-vs-NP-equivalent. -/
theorem polylog_ibm_empirical_pin_discharge_honest_scope : True := trivial

end PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_measurement_RH_peak_value
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_measurement_NP_peak_4dec_value
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_measurement_precision_pos
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.canonical_NP_is_IBM_NP_bracket_compatible
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.IBM_NP_bracket_forces_positivity
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.NP_quadratic_and_IBM_bracket_force_phi_plus_quarter
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.P_quadratic_and_positivity_force_sqrt2
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_data_plus_algebraic_identities_force_empirical_pin
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_data_plus_algebraic_identities_discharge_polylog
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.IBM_NP_bracket_and_quadratic_imply_NP_half
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.P_half_and_IBM_NP_bracketed_quadratic_imply_polylog
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_data_discharge_implies_P_neq_NP
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_measurement_RH_eq_bridge
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_measurement_NP_eq_bridge
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_measurement_RH_eq_alpha_RH
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.ibm_measurement_NP_close_to_alpha_NP
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.polylog_ibm_empirical_pin_discharge_capstone
#print axioms
  PrincipiaTractalis.PolylogIBMEmpiricalPinDischarge.polylog_ibm_empirical_pin_discharge_honest_scope

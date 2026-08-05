/-
# PF.Referee.FalsifiabilityRegistryV2

**Dated 2026-08-04. This file SUPERSEDES the F1–F8 falsifier encoding in
`PF/Referee/FrameworkFalsifiabilityConditions.lean`.**

## Why this file exists

The Codex audit of 2026-07-28
(`codex/FALSIFIABILITY_REGISTRY_DEFECT_2026-07-28.md`, independently
reviewed and confirmed the same day) found that every falsifier in the
old registry has the shape

    ∃ m : ℝ, |m − predicted| > ε

with `m` completely unconstrained. Such a proposition is inhabited by an
arbitrary real number — e.g. `H₀ = 0` satisfies the old F4 — so each old
F-condition is **mathematically true independent of any experiment**.
The old falsifiers are structurally vacuous. **They are not refutation
conditions and should not be cited as kernel-verified falsifiability
anywhere** (papers, README, six_as_one.pdf, talks).

## What this file does instead

Following the fix prescribed in the defect record, a falsifier here is a
**decidable predicate on a concrete measurement record**:

  * `Measurement` carries an exact rational value, a strictly positive
    rational tolerance, and a provenance string (instrument / dataset /
    run identifier). Provenance is data, not proof.
  * `Refutes predicted m` holds iff the measurement band
    `[m.value − m.tolerance, m.value + m.tolerance]` excludes the
    predicted rational. It is DECIDABLE: feeding a concrete measurement
    either refutes or does not, by kernel-checkable rational arithmetic
    (`norm_num`; no `native_decide` anywhere in this file).
  * `RefutesInterval lo hi m` is the bracket-claim analogue: the whole
    measurement band lies outside `[lo, hi]`.
  * Each live falsifier fixes ONE predicted rational value (anchored by
    theorem to the framework constant it comes from, by exact Lean name)
    and ONE maximum reported tolerance (the preregistered protocol
    precision) — no more per-document tolerance variants.
  * Non-vacuity is witnessed BOTH ways for every live falsifier: a
    (clearly marked HYPOTHETICAL) measurement that fires it, and a
    measurement that does not. The predicate genuinely discriminates.

## Status of the eight old falsifiers (per the defect record)

  * F1 (α_RH = 3/2, IBM benchmark)      — LIVE, rebuilt below.
  * F2 (ch₂ = 0.95 saturation)          — RETIRED: the `c₂ = 19/20`
        derivation was retracted; no defensible prediction remains.
  * F3 (Λ_eff suppression exponent)     — RETIRED: definitional identity
        masquerading as a prediction; ε unconstrained; depends on the
        retracted 0.95 anchor.
  * F4 (H₀ ∈ [67, 75] bracket)          — LIVE, rebuilt below.
  * F5 (144th-problem α coherence)      — LIVE, rebuilt below.
  * F6 (Ω_Λ ∈ [0.65, 0.75] bracket)     — LIVE, rebuilt below.
  * F7 (BRST H² = 78)                   — RESTATED as the arithmetic
        identity 78 = 48 + 26 + 4; the E₆/BRST interpretation is
        UNFORMALIZED and no measurement protocol exists. Not live.
  * F8 (micro–macro log-3 bridge)       — RETIRED: tied to the retracted
        suppression-exponent anchor; the fixed ½·log 3 tolerance and
        k = 252 were never proved.

The import of the old file below is ONLY to anchor the predicted
rational values to the framework constants by exact Lean name. None of
the old vacuous Props are re-exported, re-proved, or cited.
-/

import Mathlib.Tactic
import PF.Referee.FrameworkFalsifiabilityConditions

namespace PF.Referee.FalsifiabilityRegistryV2

/-! ## §0 — Measurement records and the decidable `Refutes` predicate -/

/-- A concrete measurement record.

    * `value`     — the reported central value, as an EXACT rational
                    (what a data release actually prints; never an
                    unconstrained real).
    * `tolerance` — the reported uncertainty (half-width of the
                    measurement band), strictly positive.
    * `source`    — provenance: instrument / dataset / run identifier.
                    This is data, not proof; it makes the record
                    auditable, it does not certify it.

    A falsifier in this registry consumes a `Measurement` and DECIDES
    (rational arithmetic, kernel-checkable) whether it refutes the
    corresponding prediction. -/
structure Measurement where
  value     : ℚ
  tolerance : ℚ
  tol_pos   : 0 < tolerance
  source    : String

/-- `Refutes predicted m`: the measurement band
    `[m.value − m.tolerance, m.value + m.tolerance]` EXCLUDES the
    predicted value. This is the faithful point-prediction refutation
    shape: it cannot be inhabited by an arbitrary witness — it is a
    decidable property of the concrete record `m`. -/
def Refutes (predicted : ℚ) (m : Measurement) : Prop :=
  predicted < m.value - m.tolerance ∨ m.value + m.tolerance < predicted

/-- `Refutes` is decidable: rational comparisons decide it. -/
instance (predicted : ℚ) (m : Measurement) : Decidable (Refutes predicted m) := by
  unfold Refutes; infer_instance

/-- Equivalence with the absolute-value form used in the defect record:
    `Refutes predicted m ↔ tolerance < |value − predicted|`. -/
theorem refutes_iff_abs (predicted : ℚ) (m : Measurement) :
    Refutes predicted m ↔ m.tolerance < |m.value - predicted| := by
  unfold Refutes
  rw [lt_abs]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; rw [neg_sub]; linarith
  · rintro (h | h)
    · left; linarith
    · rw [neg_sub] at h; right; linarith

/-- Sanity: a measurement that lands exactly on the prediction never
    refutes it (this was FALSE-by-vacuity in the old encoding, where a
    refuting witness always existed). -/
theorem prediction_not_self_refuting (p t : ℚ) (ht : 0 < t) (s : String) :
    ¬ Refutes p ⟨p, t, ht, s⟩ := by
  unfold Refutes
  push_neg
  constructor <;> simp <;> linarith

/-- `RefutesInterval lo hi m`: the measurement band lies ENTIRELY outside
    the predicted bracket `[lo, hi]`. Used for the framework's bracket
    claims (F4, F6). Decidable, like `Refutes`. -/
def RefutesInterval (lo hi : ℚ) (m : Measurement) : Prop :=
  m.value + m.tolerance < lo ∨ hi < m.value - m.tolerance

instance (lo hi : ℚ) (m : Measurement) : Decidable (RefutesInterval lo hi m) := by
  unfold RefutesInterval; infer_instance

/-! ## §1 — Registry status ledger

One machine-readable ledger recording the disposition of each of the
eight old falsifiers under this rebuild. -/

/-- Disposition of a falsifier in the V2 registry. -/
inductive FalsifierStatus where
  /-- Rebuilt on the `Measurement`/`Refutes` pattern; forward-runnable. -/
  | live (protocolNote : String)
  /-- Withdrawn; no defensible prediction remains. Not a falsifier. -/
  | retired (reason : String)
  /-- Restated as a bare arithmetic identity; physical interpretation
      unformalized. Not a falsifier. -/
  | restatedArithmetic (note : String)
  deriving Repr

/-- The V2 disposition ledger for the eight old falsifiers. -/
def registry : List (String × FalsifierStatus) :=
  [ ("F1_alphaRH",     .live "predicted 3/2; protocol precision 10^-3 (Heron-class floor)"),
    ("F2_ch2",         .retired "c2 = 19/20 derivation retracted 2026; no defensible prediction"),
    ("F3_lambdaEff",   .retired "definitional identity, unconstrained epsilon, depends on retracted c2"),
    ("F4_hubble",      .live "bracket [67, 75] km/s/Mpc; protocol precision 0.5"),
    ("F5_alpha144",    .live "targets sqrt 2 and phi + 1/4 via 10^-7-accurate rational proxies; protocol precision 10^-4"),
    ("F6_omegaLambda", .live "bracket [0.65, 0.75]; protocol precision 0.005"),
    ("F7_brstH2",      .restatedArithmetic "78 = 48 + 26 + 4 is bare arithmetic; E6/BRST reading unformalized"),
    ("F8_microMacro",  .retired "tied to retracted suppression-exponent anchor; k = 252 and half-log-3 tolerance never proved") ]

/-! ## §2 — F1 (LIVE): α_RH point prediction

The framework predicts α_RH = 3/2
(`PrincipiaTractalis.CrossMillenniumSharedInvariants.α_RH`, re-exported
as `alpha_RH_predicted` in the old registry, proved `= 3/2` there by
`alpha_RH_predicted_eq_three_halves`).

**What would refute it**: a measurement of the α_RH observable on the
preregistered 10-way IBM Quantum benchmark whose reported band
`[value − tolerance, value + tolerance]` excludes 3/2, with reported
tolerance ≤ 10⁻³.

**One tolerance, fixed here**: 10⁻³, the Heron-class (IBM 2024+
processor generation) observable-precision floor recorded in the old
file §3.5. The old file's 10⁻¹⁵ variant is DROPPED: it was orders of
magnitude beyond any hardware and made F1 untestable in practice. The
defect record requires exactly one preregistered tolerance; this is it. -/

/-- F1 predicted value: α_RH = 3/2. -/
def f1_predicted : ℚ := 3 / 2

/-- F1 preregistered maximum reported tolerance: 10⁻³ (Heron-class). -/
def f1_maxTolerance : ℚ := 1 / 1000

/-- F1 fires on `m` iff `m` meets the protocol precision gate and its
    band excludes 3/2. Decidable. -/
def F1_Refuted (m : Measurement) : Prop :=
  m.tolerance ≤ f1_maxTolerance ∧ Refutes f1_predicted m

instance (m : Measurement) : Decidable (F1_Refuted m) := by
  unfold F1_Refuted; infer_instance

/-- Anchor: the registry's rational 3/2 IS the framework constant, by
    exact Lean name. -/
theorem f1_anchor :
    ((f1_predicted : ℚ) : ℝ) =
      PF.Referee.FrameworkFalsifiabilityConditions.alpha_RH_predicted := by
  rw [PF.Referee.FrameworkFalsifiabilityConditions.alpha_RH_predicted_eq_three_halves]
  norm_num [f1_predicted]

/-- Non-vacuity (fires). **HYPOTHETICAL DATA — not a real measurement.**
    A band 1.492 ± 0.001 excludes 3/2, so F1 would fire on it. -/
theorem f1_fires_on_discrepant_band :
    F1_Refuted ⟨1492 / 1000, 1 / 1000, by norm_num,
      "HYPOTHETICAL: illustrative discrepant run; no such measurement exists"⟩ := by
  unfold F1_Refuted Refutes f1_predicted f1_maxTolerance
  norm_num

/-- Non-vacuity (does not fire). **HYPOTHETICAL DATA.** A band
    1.4999 ± 0.001 contains 3/2, so F1 does not fire: the predicate
    genuinely discriminates. -/
theorem f1_silent_on_consistent_band :
    ¬ F1_Refuted ⟨14999 / 10000, 1 / 1000, by norm_num,
      "HYPOTHETICAL: illustrative consistent run"⟩ := by
  unfold F1_Refuted Refutes f1_predicted f1_maxTolerance
  norm_num

/-! ## §3 — F2 (RETIRED), F3 (RETIRED)

**F2 (ch₂ = 0.95 saturation): RETIRED 2026-08-04.**
The `c₂ = 19/20` derivation behind `threshold_ch2` was retracted (see
the defect record's per-condition table and the True-Prop/c₂ audit
trail). With the derivation retracted there is no defensible predicted
rational to register, so per the honesty rule of this file F2 is
encoded as RETIRED, not as a live falsifier with an invented number.
No `F2_Refuted` exists in this registry by design.

**F3 (Λ_eff suppression exponent): RETIRED 2026-08-04.**
The old F3 compared a measurement against `exp(−78π · 0.95 · 1.1875)`
where the compared quantity was DEFINED by that same exponential — a
definitional identity, not a prediction — with an unconstrained ε that
could even be ≤ 0. It also inherits the retracted 0.95 anchor.
No `F3_Refuted` exists in this registry by design. -/

/-! ## §4 — F4 (LIVE): Hubble bracket claim

The framework's commitment (old registry, v2-edition 2026-06-03) is the
BRACKET `H₀ ∈ [67, 75]` km/s/Mpc with midpoint prediction 69.8
(`PrincipiaTractalis.Cosmology.LambdaCDMRebuttal.hubble_framework_prediction`).

**What would refute it**: a combined H₀ determination (CMB-S4 / Simons
Observatory × JWST distance ladder × DESI BAO class) whose reported band
lies entirely below 67 or entirely above 75, with reported tolerance
≤ 0.5 km/s/Mpc (protocol P4's stated precision).

Bracket provenance note: the bracket was widened [67, 73] → [67, 75] on
2026-06-03 to accommodate the LDN 2025 consensus (arXiv:2510.23823).
That drift is on record in the old file; this registry freezes the
CURRENT bracket [67, 75] as the single registered commitment. -/

/-- F4 bracket lower edge: 67 km/s/Mpc. -/
def f4_lo : ℚ := 67

/-- F4 bracket upper edge: 75 km/s/Mpc. -/
def f4_hi : ℚ := 75

/-- F4 midpoint prediction: 69.8 = 349/5 km/s/Mpc. -/
def f4_predicted_midpoint : ℚ := 349 / 5

/-- F4 preregistered maximum reported tolerance: 0.5 km/s/Mpc. -/
def f4_maxTolerance : ℚ := 1 / 2

/-- F4 fires on `m` iff `m` meets the protocol precision gate and its
    band lies entirely outside `[67, 75]`. Decidable. -/
def F4_Refuted (m : Measurement) : Prop :=
  m.tolerance ≤ f4_maxTolerance ∧ RefutesInterval f4_lo f4_hi m

instance (m : Measurement) : Decidable (F4_Refuted m) := by
  unfold F4_Refuted; infer_instance

/-- Anchor: the registry's rational 349/5 IS the framework constant
    69.8, by exact Lean name. -/
theorem f4_anchor :
    ((f4_predicted_midpoint : ℚ) : ℝ) =
      PF.Referee.FrameworkFalsifiabilityConditions.hubble_predicted := by
  unfold PF.Referee.FrameworkFalsifiabilityConditions.hubble_predicted
    PrincipiaTractalis.Cosmology.LambdaCDMRebuttal.hubble_framework_prediction
  norm_num [f4_predicted_midpoint]

/-- Non-vacuity (does not fire) on REAL published data: Planck 2018
    H₀ = 67.4 ± 0.5 km/s/Mpc (Aghanim et al., A&A 641, A6 (2020), as
    recorded in the PF corpus constant `hubble_CMB_Planck = 67.4`).
    Band [66.9, 67.9] overlaps [67, 75], so F4 does not fire. -/
theorem f4_silent_on_planck2018 :
    ¬ F4_Refuted ⟨674 / 10, 5 / 10, by norm_num,
      "REAL: Planck 2018, Aghanim et al. A&A 641 A6 (2020), H0 = 67.4 +/- 0.5 km/s/Mpc"⟩ := by
  unfold F4_Refuted RefutesInterval f4_lo f4_hi f4_maxTolerance
  norm_num

/-- Non-vacuity (fires). **HYPOTHETICAL DATA — not a real measurement.**
    A band 65.0 ± 0.3 lies entirely below 67, so F4 would fire on it. -/
theorem f4_fires_on_low_band :
    F4_Refuted ⟨65, 3 / 10, by norm_num,
      "HYPOTHETICAL: illustrative low-H0 determination; no such measurement exists"⟩ := by
  unfold F4_Refuted RefutesInterval f4_lo f4_hi f4_maxTolerance
  norm_num

/-! ## §5 — F5 (LIVE): 144th-problem α coherence

The framework claims every problem in the 143-problem corpus has
α ∈ {√2, φ + 1/4} and predicts a preregistered 144th problem will too.

**Irrational targets, rational registry**: √2 and φ + 1/4 are
irrational, so this ℚ-registry uses rational PROXIES accurate to
better than 10⁻⁶ — two orders of magnitude finer than the 10⁻⁴
protocol precision (P2), so the proxy error can never flip a
refutation decision at protocol tolerance. The proxy accuracy is
PROVED below (`f5_sqrt2_ref_anchor`, `f5_phiQuarter_ref_anchor`)
against `Real.sqrt 2` and `PrincipiaTractalis.phi + 1/4` by exact
Lean name — the proxies are theorems, not free parameters.

**What would refute it**: a 144th-problem α measurement (preregistered
selection protocol, same α-extraction pipeline as the 143 corpus, reported
tolerance ≤ 10⁻⁴) whose band excludes BOTH targets. -/

/-- F5 rational proxy for √2: 1.4142136 (within 10⁻⁶ of √2, proved
    below). -/
def f5_sqrt2_ref : ℚ := 14142136 / 10000000

/-- F5 rational proxy for φ + 1/4: 1.868034 (within 10⁻⁶ of the target,
    proved below). -/
def f5_phiQuarter_ref : ℚ := 1868034 / 1000000

/-- F5 preregistered maximum reported tolerance: 10⁻⁴ (protocol P2's
    stated α-extraction precision). -/
def f5_maxTolerance : ℚ := 1 / 10000

/-- F5 fires on `m` iff `m` meets the protocol precision gate and its
    band excludes BOTH admissible targets. Decidable. -/
def F5_Refuted (m : Measurement) : Prop :=
  m.tolerance ≤ f5_maxTolerance ∧
    Refutes f5_sqrt2_ref m ∧ Refutes f5_phiQuarter_ref m

instance (m : Measurement) : Decidable (F5_Refuted m) := by
  unfold F5_Refuted; infer_instance

/-- √2 bracket used to certify the F5 proxy. -/
theorem f5_sqrt2_bounds :
    (14142135 : ℝ) / 10000000 < Real.sqrt 2 ∧
      Real.sqrt 2 < (14142136 : ℝ) / 10000000 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnn := Real.sqrt_nonneg 2
  constructor
  · nlinarith [h, hnn]
  · nlinarith [h, hnn]

/-- Anchor: the F5 proxy is within 10⁻⁶ of the true target √2. -/
theorem f5_sqrt2_ref_anchor :
    |Real.sqrt 2 - ((f5_sqrt2_ref : ℚ) : ℝ)| < 1 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := f5_sqrt2_bounds
  have hcast : ((f5_sqrt2_ref : ℚ) : ℝ) = 14142136 / 10000000 := by
    norm_num [f5_sqrt2_ref]
  rw [hcast, abs_sub_lt_iff]
  constructor <;> linarith

/-- √5 bracket used to certify the F5 proxy for φ + 1/4. -/
theorem f5_sqrt5_bounds :
    (22360679 : ℝ) / 10000000 < Real.sqrt 5 ∧
      Real.sqrt 5 < (22360680 : ℝ) / 10000000 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hnn := Real.sqrt_nonneg 5
  constructor
  · nlinarith [h, hnn]
  · nlinarith [h, hnn]

/-- Anchor: the F5 proxy is within 10⁻⁶ of the true target φ + 1/4,
    with φ the framework's `PrincipiaTractalis.phi = (1 + √5)/2` by
    exact Lean name. -/
theorem f5_phiQuarter_ref_anchor :
    |(PrincipiaTractalis.phi + 1 / 4) - ((f5_phiQuarter_ref : ℚ) : ℝ)| < 1 / 1000000 := by
  obtain ⟨hlo, hhi⟩ := f5_sqrt5_bounds
  have hphi : PrincipiaTractalis.phi = (1 + Real.sqrt 5) / 2 := rfl
  have hcast : ((f5_phiQuarter_ref : ℚ) : ℝ) = 1868034 / 1000000 := by
    norm_num [f5_phiQuarter_ref]
  rw [hphi, hcast, abs_sub_lt_iff]
  constructor <;> linarith

/-- Non-vacuity (fires). **HYPOTHETICAL DATA — not a real measurement.**
    A 144th-problem band 1.7 ± 0.0001 excludes both targets, so F5
    would fire on it. -/
theorem f5_fires_on_off_target_band :
    F5_Refuted ⟨17 / 10, 1 / 10000, by norm_num,
      "HYPOTHETICAL: illustrative off-target 144th-problem alpha; no such measurement exists"⟩ := by
  unfold F5_Refuted Refutes f5_sqrt2_ref f5_phiQuarter_ref f5_maxTolerance
  norm_num

/-- Non-vacuity (does not fire). **HYPOTHETICAL DATA.** A band
    1.4142136 ± 0.0001 contains the √2 proxy, so F5 does not fire. -/
theorem f5_silent_on_sqrt2_band :
    ¬ F5_Refuted ⟨14142136 / 10000000, 1 / 10000, by norm_num,
      "HYPOTHETICAL: illustrative on-target 144th-problem alpha"⟩ := by
  unfold F5_Refuted Refutes f5_sqrt2_ref f5_phiQuarter_ref f5_maxTolerance
  norm_num

/-! ## §6 — F6 (LIVE): dark-energy density bracket claim

The framework's commitment is the BRACKET `Ω_Λ ∈ [0.65, 0.75]` with
point prediction 0.7 (`PrincipiaTractalis.Wave58.darkEnergyDensity`,
proved `= 0.7` in the old registry).

**What would refute it**: an Ω_Λ determination (DESI BAO year-5 +
Pantheon+ extension + LSST weak lensing class) whose reported band lies
entirely outside `[0.65, 0.75]`, with reported tolerance ≤ 0.005
(protocol P5's stated precision). -/

/-- F6 bracket lower edge: 0.65 = 13/20. -/
def f6_lo : ℚ := 13 / 20

/-- F6 bracket upper edge: 0.75 = 3/4. -/
def f6_hi : ℚ := 3 / 4

/-- F6 point prediction: Ω_Λ = 0.7 = 7/10. -/
def f6_predicted : ℚ := 7 / 10

/-- F6 preregistered maximum reported tolerance: 0.005 = 1/200. -/
def f6_maxTolerance : ℚ := 1 / 200

/-- F6 fires on `m` iff `m` meets the protocol precision gate and its
    band lies entirely outside `[0.65, 0.75]`. Decidable. -/
def F6_Refuted (m : Measurement) : Prop :=
  m.tolerance ≤ f6_maxTolerance ∧ RefutesInterval f6_lo f6_hi m

instance (m : Measurement) : Decidable (F6_Refuted m) := by
  unfold F6_Refuted; infer_instance

/-- Anchor: the registry's rational 7/10 IS the framework constant 0.7,
    by exact Lean name. -/
theorem f6_anchor :
    ((f6_predicted : ℚ) : ℝ) =
      PF.Referee.FrameworkFalsifiabilityConditions.darkEnergyDensity_predicted := by
  rw [PF.Referee.FrameworkFalsifiabilityConditions.darkEnergyDensity_predicted_eq_0_7]
  norm_num [f6_predicted]

/-- Non-vacuity (does not fire) on REAL published data: Planck 2018
    Ω_Λ = 0.6847 ± 0.0073 (Aghanim et al., A&A 641, A6 (2020)).
    Note this record does NOT meet the 0.005 precision gate (0.0073 >
    0.005) — and its band also sits inside the bracket, as
    `f6_planck2018_band_inside_bracket` shows independently of the
    gate. Either way F6 does not fire. -/
theorem f6_silent_on_planck2018 :
    ¬ F6_Refuted ⟨6847 / 10000, 73 / 10000, by norm_num,
      "REAL: Planck 2018, Aghanim et al. A&A 641 A6 (2020), OmegaLambda = 0.6847 +/- 0.0073"⟩ := by
  unfold F6_Refuted RefutesInterval f6_lo f6_hi f6_maxTolerance
  norm_num

/-- The Planck 2018 Ω_Λ band lies inside the bracket — the non-firing
    above is not an artifact of the precision gate. (Same REAL data.) -/
theorem f6_planck2018_band_inside_bracket :
    ¬ RefutesInterval f6_lo f6_hi ⟨6847 / 10000, 73 / 10000, by norm_num,
      "REAL: Planck 2018, Aghanim et al. A&A 641 A6 (2020), OmegaLambda = 0.6847 +/- 0.0073"⟩ := by
  unfold RefutesInterval f6_lo f6_hi
  norm_num

/-- Non-vacuity (fires). **HYPOTHETICAL DATA — not a real measurement.**
    A band 0.600 ± 0.004 lies entirely below 0.65, so F6 would fire. -/
theorem f6_fires_on_low_band :
    F6_Refuted ⟨6 / 10, 1 / 250, by norm_num,
      "HYPOTHETICAL: illustrative low-OmegaLambda determination; no such measurement exists"⟩ := by
  unfold F6_Refuted RefutesInterval f6_lo f6_hi f6_maxTolerance
  norm_num

/-! ## §7 — F7 (RESTATED): the honest arithmetic content

Per the defect record (required action 5), F7 either constructs the
BRST cohomology — a large unstarted project — or is restated honestly.
This registry restates it:

**What is formalized**: the arithmetic identity `78 = 48 + 26 + 4`.
Nothing more.

**What is NOT formalized**: any BRST complex, any cohomology group,
any connection to dim E₆, any measurement protocol. The old F7's
"∃ n : ℕ, n ≠ 78" was vacuously true (witness: 0) and its "LHC
protocol" had no operational content. There is NO live F7 falsifier in
this registry because there is nothing measurable to register. -/

/-- The entire formalized content of old F7: bare arithmetic. The
    E₆/BRST interpretation is unformalized and carries no kernel
    weight. -/
theorem f7_arithmetic_content : (78 : ℕ) = 48 + 26 + 4 := by norm_num

/-! ## §8 — F8 (RETIRED)

**F8 (micro–macro log-3 bridge): RETIRED 2026-08-04.**
The old F8 quantified over an unconstrained δ and was tied to the
suppression exponent `78π · 0.95 · 1.1875`, which inherits the retracted
`c₂ = 0.95` anchor (as does F3 — the old file itself notes F3 and F8
"stand or fall together"). The documented fixed tolerance ½·log 3 and
the specific k = 252 were never proved. No defensible prediction
remains; no `F8_Refuted` exists in this registry by design. -/

/-! ## §9 — Axiom audit

Every declaration below must use no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, no `native_decide`, no new axioms. -/

#print axioms Refutes
#print axioms RefutesInterval
#print axioms refutes_iff_abs
#print axioms prediction_not_self_refuting
#print axioms registry
#print axioms F1_Refuted
#print axioms f1_anchor
#print axioms f1_fires_on_discrepant_band
#print axioms f1_silent_on_consistent_band
#print axioms F4_Refuted
#print axioms f4_anchor
#print axioms f4_silent_on_planck2018
#print axioms f4_fires_on_low_band
#print axioms F5_Refuted
#print axioms f5_sqrt2_bounds
#print axioms f5_sqrt2_ref_anchor
#print axioms f5_sqrt5_bounds
#print axioms f5_phiQuarter_ref_anchor
#print axioms f5_fires_on_off_target_band
#print axioms f5_silent_on_sqrt2_band
#print axioms F6_Refuted
#print axioms f6_anchor
#print axioms f6_silent_on_planck2018
#print axioms f6_planck2018_band_inside_bracket
#print axioms f6_fires_on_low_band
#print axioms f7_arithmetic_content

end PF.Referee.FalsifiabilityRegistryV2

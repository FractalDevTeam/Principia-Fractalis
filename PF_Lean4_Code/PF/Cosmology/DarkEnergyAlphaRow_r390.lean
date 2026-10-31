/-
# r390: the dark-energy α-row, filled — and five of nine classes die on internal grounds

★ 2026-10-30 r390 — the DE row, pre-registered ★

## What was asked, and the one thing that made it answerable

"Give dark energy an α-row." THE MAP §3 says what a row costs: name the measured
quantity `Q_X`, the variable `v` it scales in, and the law `Q_X ∝ v^{σ(α_X)}`.
Filling a row is a **physics posit**, not a derivation, and this file is labelled
accordingly throughout.

The thing that makes it answerable without inventing a number: **there is no
tenth α to invent.** `PF.lean:836` records that the nine α-values *"exhaust the
substrate-permissible combinations over the 4-element minimal basis under the
13-condition minimal hypothesis set"* — the basis `{1, π, φ, √2}` is intrinsic
and the combinations are closed. So a new sector cannot receive a fresh α; it
receives one by **classification into an existing class**. That is exactly the
documented mechanism for the 144th problem, via
`canonicalAlpha : ProblemClass → ℝ`.

It is also where the corpus has already been burned once. The graph-isomorphism
assignment was **superseded** because its rationale — "GI is in NP and not known
to be in P" — was *"literally true of every NP problem and therefore
underdetermined"* (`ProblemClassTriClass_2026_06_22`). A classification needs a
rationale that discriminates. So this file does not pick one; it **pre-registers
all nine** and eliminates on grounds that are internal to PF and fixed before
any datum is consulted.

## The row

* `Q_DE` = the dark-energy density `ρ_DE`;
* `v` = the scale factor `a`;
* law: `ρ_DE ∝ a^{σ(α_DE)}`.

The standard parameterisation of a dark-energy fluid is `ρ_DE ∝ a^{−3(1+w)}`, so
the law **identifies** `σ(α_DE) = −3(1 + w)`, i.e.

    w₀ = −1 − σ(α_DE)/3        (`wOfSigma`)

This is the direct analogue of the QG row, which used the standard
parameterisation `P(k) ∝ k^{n_s−1}` and read `n_s − 1` off as the exponent. No
freedom was taken: `−3(1+w)` is *the* exponent of `a` in `ρ_DE`, as `n_s − 1` is
*the* exponent of `k` in `P(k)`.

## The gate, which is internal and prior

PF's own action derivation (`codex/COSMOLOGY_DE_DERIVATION_2026-10-11.md`)
proves, register A, that on the derived `Q = 0` branch
`w = (½φ̇² − V)/(½φ̇² + V) ≥ −1` — **never phantom**. Through the law that is

    w ≥ −1   ⟺   σ(α_DE) ≤ 0

(`nonphantom_iff_sigma_nonpos`). So **every class whose σ is positive is excluded
before any measurement is looked at.** r231's `corpus_sigma_sign_dichotomy`
already supplies every sign, kernel-verified, so the elimination is a theorem
and not a judgement:

| class | σ sign (r231) | `w₀` predicted | verdict |
|---|---|---|---|
| YM | `= 1` | `−1.3333` | **EXCLUDED** — phantom |
| NP | `> 0` | `−1.3157` | **EXCLUDED** — phantom |
| BSD | `> 0` | `−1.1904` | **EXCLUDED** — phantom |
| **Hodge** | `> 0` | `−1.1654` | **EXCLUDED** — phantom |
| Poincaré | `= 0` | `−1` exactly | survives |
| RH | `= 0` | `−1` exactly | survives |
| QG | `< 0` | `−0.9871` | survives |
| P | `< 0` | `−0.7693` | survives |
| NS | `< 0` | `−0.5640` | survives |

**The Hodge class is the only one carrying the golden ratio** (`α_Hodge = φ`),
and it is excluded. So the golden-ratio route into dark energy dies a second
time, on internal grounds and before data: r389 showed `−φ/2` is not a σ-value
and sits outside the derived window; this shows that even the *correct* use of
`α_Hodge = φ` — feeding it through σ — gives a phantom `w` that PF's own theorem
forbids.

The two `σ = 0` classes are also worth naming: they predict `w₀ = −1` **exactly**
(`wOfSigma_zero`), i.e. a pure cosmological constant with no evolution at all.

## Honesty about what remains, which is the important part

Four classes are eliminated by theorem. **Five survive, and choosing among them
by which one matches the data would be fitting, not prediction** — precisely the
cherry-picking THE MAP §3.2 warns against when it refuses to rescue the NS row by
inventing a better-fitting observable after seeing the miss. So the five stand
together as the row's content, and the comparison is reported, not resolved:

* PF's **own** action derivation gives `w₀ ∈ [−0.99, −0.93]`. Of the survivors
  only **QG** (`−0.9871`) lands inside it. Poincaré/RH at exactly `−1` fall just
  below; P and NS are far outside.
* The corpus's **measured** `g` inversion gives `w₀ ∈ [−0.753, −0.650]`.
  **No survivor lands inside.** P (`−0.7693`) is nearest and still below the
  floor.

That `QG` is selected by consistency with PF's *other* channel rather than by the
data is a cross-channel argument, not a fit — but it is also not a confirmation,
and it carries a consequence that should be stated because it is sharply
falsifiable: if DE and QG share a class they share one σ, so

    n_s − 1  =  −3(1 + w₀)

tying the primordial tilt to the dark-energy equation of state. With Planck's
`n_s − 1 = −0.0351 ± 0.0042` that is `w₀ = −0.9883 ± 0.0014` — near-ΛCDM, and in
sharp tension with DESI's preference for `w₀ ≈ −0.67`. **PF's two internal
channels agree with each other and both disagree with the data.** That is the
honest state of the row.

## Joint-test scoreboard, updated

THE MAP's running scoreboard was one hit (QG, 0.86σ) and one clear miss (NS,
0.36 off), with its own verdict that the joint test "does not support the map"
and "as of now it reads coincidence". This row does not change that verdict and
does not add a third datum: it adds a *pre-registration* plus four
theorem-backed eliminations. The row becomes a prediction only once the class is
fixed, and fixing it on present evidence would be fitting.

## What is NOT claimed

Not claimed: a derivation. The classification of DE into any class is a posit,
the α-values are ASSERTED postulates, and "σ is a scaling exponent" is THE MAP's
EMPIRICAL HYPOTHESIS. Not claimed: that QG is the right class — only that it is
the single survivor consistent with PF's own derived window. Not claimed: that
the exhaustion claim at `PF.lean:836` is itself beyond question; this file *uses*
it, and if a tenth α is ever admitted the elimination argument here is unaffected
but the "classification only" framing would need revisiting. Not claimed:
anything about physical spacetime.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-30.
-/
import PF.CorpusSigmaSignDichotomy_r231

set_option autoImplicit false

open scoped Real

namespace PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.CorpusSigmaSignDichotomy
open PrincipiaTractalis

/-! ## §1 — The row's law

`ρ_DE ∝ a^{σ}` against the standard `ρ_DE ∝ a^{−3(1+w)}` identifies
`σ = −3(1+w)`, inverted here. -/

/-- The dark-energy equation of state implied by a scaling exponent `σ`, through
`ρ_DE ∝ a^{−3(1+w)}`. -/
noncomputable def wOfSigma (s : ℝ) : ℝ := -1 - s / 3

/-- The inverse reading: `σ = −3(1+w)`. -/
theorem sigma_of_wOfSigma (s : ℝ) : -3 * (1 + wOfSigma s) = s := by
  unfold wOfSigma; ring

/-- A vanishing exponent is a pure cosmological constant. -/
theorem wOfSigma_zero : wOfSigma 0 = -1 := by
  unfold wOfSigma; ring

/-! ## §2 — The gate: non-phantom ⟺ `σ ≤ 0`

PF's action derivation proves `w ≥ −1` on the derived branch. Through the law
that is exactly a sign condition on σ, so it eliminates classes without
reference to any measurement. -/

/-- **The gate.** -/
theorem nonphantom_iff_sigma_nonpos (s : ℝ) : -1 ≤ wOfSigma s ↔ s ≤ 0 := by
  unfold wOfSigma
  constructor <;> intro h <;> linarith

/-- A positive exponent is phantom, hence forbidden by the derivation. -/
theorem phantom_of_sigma_pos {s : ℝ} (hs : 0 < s) : wOfSigma s < -1 := by
  unfold wOfSigma; linarith

/-! ## §3 — Four classes die, Hodge among them

Applied to r231's kernel-verified sign dichotomy. Nothing here is a new sign
computation; the signs are r212 and r225–r230, bundled by r231. -/

/-- **★★★ r390: the four growth classes cannot carry dark energy ★★★**

`YM`, `Hodge`, `NP`, `BSD` all have `σ > 0`, so each gives `w₀ < −1`, which PF's
own action derivation forbids. **`Hodge` is the only class carrying the golden
ratio**, so this is where the golden-ratio route into dark energy ends. -/
theorem growth_classes_excluded (A φ₀ : ℝ) (hA : A ≠ 0) :
    wOfSigma (SO_αYM A φ₀ hA).sigma < -1
      ∧ wOfSigma (SO_αHodge A φ₀ hA).sigma < -1
      ∧ wOfSigma (SO_αNP A φ₀ hA).sigma < -1
      ∧ wOfSigma (SO_αBSD A φ₀ hA).sigma < -1 := by
  obtain ⟨hYM, hHodge, hNP, hBSD, -⟩ := corpus_sigma_sign_dichotomy A φ₀ hA
  refine ⟨?_, phantom_of_sigma_pos hHodge, phantom_of_sigma_pos hNP,
    phantom_of_sigma_pos hBSD⟩
  exact phantom_of_sigma_pos (by rw [hYM]; norm_num)

/-- The `Hodge` exclusion, isolated — the golden-ratio class specifically. -/
theorem hodge_class_excluded_for_dark_energy (A φ₀ : ℝ) (hA : A ≠ 0) :
    ¬ (-1 ≤ wOfSigma (SO_αHodge A φ₀ hA).sigma) := by
  obtain ⟨-, hHodge, -⟩ := corpus_sigma_sign_dichotomy A φ₀ hA
  exact not_le.mpr (phantom_of_sigma_pos hHodge)

/-! ## §4 — The survivors, and the two that pin `w = −1` exactly -/

/-- The `σ = 0` classes predict a pure cosmological constant. -/
theorem flat_classes_give_cosmological_constant (A φ₀ : ℝ) (hA : A ≠ 0) :
    wOfSigma (SO_αPoincare A φ₀ hA).sigma = -1
      ∧ wOfSigma (SO_αRH A φ₀ hA).sigma = -1 := by
  obtain ⟨-, -, -, -, hPo, hRH, -⟩ := corpus_sigma_sign_dichotomy A φ₀ hA
  exact ⟨by rw [hPo, wOfSigma_zero], by rw [hRH, wOfSigma_zero]⟩

/-- The `σ < 0` classes are the non-trivially non-phantom survivors. -/
theorem decay_classes_survive_gate (A φ₀ : ℝ) (hA : A ≠ 0) :
    -1 < wOfSigma (SO_αP A φ₀ hA).sigma
      ∧ -1 < wOfSigma (SO_αQG A φ₀ hA).sigma
      ∧ -1 < wOfSigma (SO_αNS A φ₀ hA).sigma := by
  obtain ⟨-, -, -, -, -, -, hP, hQG, hNS⟩ := corpus_sigma_sign_dichotomy A φ₀ hA
  unfold wOfSigma
  exact ⟨by linarith, by linarith, by linarith⟩

end PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.sigma_of_wOfSigma
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.wOfSigma_zero
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.nonphantom_iff_sigma_nonpos
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.phantom_of_sigma_pos
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.growth_classes_excluded
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.hodge_class_excluded_for_dark_energy
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.flat_classes_give_cosmological_constant
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.decay_classes_survive_gate

-- Axiom-check coverage completed 2026-10-30 (declarations the in-file check had omitted)
#print axioms PrincipiaTractalis.Cosmology.DarkEnergyAlphaRow.wOfSigma

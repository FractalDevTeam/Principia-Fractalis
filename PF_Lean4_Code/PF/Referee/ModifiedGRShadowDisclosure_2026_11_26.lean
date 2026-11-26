/-
# The modified-GR shadow, disclosed in the kernel

Four Prop names are defined TWICE in this corpus, in a parent namespace and a
child namespace, with different bodies:

  | name                                        | `PrincipiaTractalis`                        | `…GeneralRelativityContentful`        |
  |---------------------------------------------|---------------------------------------------|---------------------------------------|
  | `ModifiedEinsteinWithConsciousnessHypothesis`| `∃ L G, L = L ∧ G = G ∧ True`               | Bianchi ⟹ combined conservation, ∀ D  |
  | `EnergyInformationEquivalenceHypothesis`     | `∃ c², 0 < c²`                              | budget-conservation equivalence       |
  | `DarkEnergyAsLambdaEffHypothesis`            | `∃ L₀ Lₑ, 0 < L₀ ∧ 0 ≤ Lₑ ∧ Lₑ ≤ L₀`        | `lambdaEff` boundary + strict antitone|
  | `ModifiedGRWithConsciousnessBundle`          | the conjunction of the three above          | the conjunction of the three above    |

The last row is the dangerous one: the bundle's source text is **byte-identical**
in both files, and means two different things depending on which namespace reads
it. `PF.TheoreticalPhysics_FrameworkBundle` did `open PrincipiaTractalis` and
imported only `PF.GeneralRelativity`, so its conjunct (T1) resolved to the
placeholder. Every axiom and `sorry` gate reported it clean and proved on
`[propext, Classical.choice, Quot.sound]`, because it *is* clean and proved ---
it just says nothing. That conjunct is repointed (same commit); this file makes
the emptiness impossible to re-hide.

## Measured before acting

Corpus-wide: of **1081** distinct `def _ : Prop` names across **10874** files,
only **9** are defined in more than one module. Four are this GR family. Three
are `True` anchors in the Referee disclosure files, which are deliberate and
already self-disclosing. Two were false positives of my own extractor --- a
docstring *quoting* a definition, counted as a second definition. So the
shadowing class is exactly this one family. It does not generalise and no
further hunt is owed.

## What is proved

Each placeholder is shown **equivalent to `True`**, which is the sharp
instrument: a Prop provably equivalent to `True` carries zero information, and
saying so in the kernel is stronger than any comment. Nothing is renamed and
nothing is withdrawn --- the placeholders keep their names and their `_holds`
theorems, exactly as the Andrews–Curtis and anchor disclosures did.

Against that, the contentful side is shown **not to be a tautology**, and not by
assertion: `combined_divergence_needs_metric_compatibility` and
`combined_divergence_needs_bianchi` prove that dropping either hypothesis makes
the statement FALSE. A statement whose hypotheses are each load-bearing is not
vacuous; a statement equivalent to `True` is. That is the whole distinction, and
it is checkable.

## What is NOT claimed

Both bundles are true, so they are propositionally equivalent and this file does
NOT claim otherwise --- claiming the two Props are "inequivalent" would be
false. The claim is about information content: one is a tautology, the other has
necessary hypotheses. Nor does anything here assert the physics; the contentful
Props are statements about ℝ-linear divergence operators and real-valued
budgets, standing in for tensor content that cannot be written at a mathlib pin
with Lorentzian, PseudoRiemannian, LeviCivita, RicciTensor and MetricTensor all
at 0 files (measured 2026-11-26).
-/

import PF.GeneralRelativityContentful_2026_10_08
import PF.TheoreticalPhysics_FrameworkBundle

set_option autoImplicit false

namespace PF.Referee.ModifiedGRShadowDisclosure

/-! ## §1 Each placeholder is a tautology -/

/-- The placeholder modified-Einstein hypothesis carries no information. -/
theorem placeholder_modifiedEinstein_iff_True :
    PrincipiaTractalis.ModifiedEinsteinWithConsciousnessHypothesis ↔ True :=
  iff_true_intro PrincipiaTractalis.ModifiedEinsteinWithConsciousnessHypothesis_holds

/-- The placeholder energy-information hypothesis carries no information. -/
theorem placeholder_energyInformation_iff_True :
    PrincipiaTractalis.EnergyInformationEquivalenceHypothesis ↔ True :=
  iff_true_intro PrincipiaTractalis.EnergyInformationEquivalenceHypothesis_holds

/-- The placeholder dark-energy hypothesis carries no information. -/
theorem placeholder_darkEnergy_iff_True :
    PrincipiaTractalis.DarkEnergyAsLambdaEffHypothesis ↔ True :=
  iff_true_intro PrincipiaTractalis.DarkEnergyAsLambdaEffHypothesis_holds

/-- **★ The placeholder BUNDLE carries no information. ★** This is the Prop that
    a framework capstone used as its conjunct (T1). -/
theorem placeholder_bundle_iff_True :
    PrincipiaTractalis.ModifiedGRWithConsciousnessBundle ↔ True :=
  iff_true_intro PrincipiaTractalis.ModifiedGRWithConsciousnessBundle_consistent

/-! ## §2 The contentful side is not a tautology

Wired by inferred type: the statements are not transcribed, they are the
upstream theorems themselves, so these cannot drift from what was proved. -/

/-- Metric compatibility is load-bearing: drop `D g = 0` and the combined
    conservation statement is FALSE. -/
def contentful_needs_metric_compatibility :=
  PrincipiaTractalis.GeneralRelativityContentful.combined_divergence_needs_metric_compatibility

/-- The Bianchi hypothesis is load-bearing: drop `D G = 0` and the combined
    conservation statement is FALSE. -/
def contentful_needs_bianchi :=
  PrincipiaTractalis.GeneralRelativityContentful.combined_divergence_needs_bianchi

/-- The contentful bundle holds. -/
theorem contentful_bundle_holds :
    PrincipiaTractalis.GeneralRelativityContentful.ModifiedGRWithConsciousnessBundle :=
  PrincipiaTractalis.GeneralRelativityContentful.ModifiedGRWithConsciousnessBundle_holds

/-! ## §3 The capstone now carries the contentful conjunct

`framework_theoretical_physics_support_bundle` is re-exported here by inferred
type. Its (T1) is the fully-qualified contentful bundle as of 2026-11-26, so if
anyone ever repoints it back at the placeholder this alias still typechecks but
the disclosure above stands beside it. -/

def framework_bundle_as_gated :=
  PrincipiaTractalis.TheoreticalPhysics_FrameworkBundle.framework_theoretical_physics_support_bundle

/-! ## §4 Capstone -/

/-- **★ THE SHADOW, DISCLOSED. ★**

    All four placeholder Props are tautologies; the contentful bundle holds; and
    the contentful side has two hypotheses that are each necessary, so it is not
    vacuous. Every conjunct is proved above. -/
theorem the_modified_gr_shadow :
    (PrincipiaTractalis.ModifiedEinsteinWithConsciousnessHypothesis ↔ True)
      ∧ (PrincipiaTractalis.EnergyInformationEquivalenceHypothesis ↔ True)
      ∧ (PrincipiaTractalis.DarkEnergyAsLambdaEffHypothesis ↔ True)
      ∧ (PrincipiaTractalis.ModifiedGRWithConsciousnessBundle ↔ True)
      ∧ PrincipiaTractalis.GeneralRelativityContentful.ModifiedGRWithConsciousnessBundle :=
  ⟨placeholder_modifiedEinstein_iff_True,
   placeholder_energyInformation_iff_True,
   placeholder_darkEnergy_iff_True,
   placeholder_bundle_iff_True,
   contentful_bundle_holds⟩

end PF.Referee.ModifiedGRShadowDisclosure

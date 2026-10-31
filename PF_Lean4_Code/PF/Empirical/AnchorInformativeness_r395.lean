/-
# r395: why one IBM anchor is informative and the other cannot be — rationality decides

★ 2026-10-30 r395 — the unflagged twin of the corpus's highest referee risk ★

## What this file is about

ch21's verification ledger (`ch21_p_vs_np.tex:1527`) records:

> **CIRCULAR — the "IBM empirical validation"** —
> `framework_alpha_NP_matches_IBM_empirical_peak`, whose docstring says the
> value "matches the IBM Quantum hardware-measured NP peak EXACTLY," is proved
> by `:= rfl`. … No measurement enters the theorem; it is a definition compared
> with itself. The audit flags this as **the single highest referee risk in the
> corpus**.

That flag is correct, and it has a **twin that is flagged nowhere**. Searched
across `codex/*.md`, `MISSION_INVENTORY/*.md` and every chapter: `ibm_peak_RH`,
`IBMEmpiricalAlphaTableBridge` and `IBMAlphaRHEmpiricalAnchor` return **zero
hits**. In that file

    ibm_peak_RH : ℝ := 3 / 2                       -- "IBM 4-decimal measured peak"
    ibm_peak_RH_eq_alpha_RH : ibm_peak_RH = alpha_RH := by unfold …; rfl

so the RH "empirical anchor" is `3/2 = 3/2`, closed by `rfl`, and its docstring
calls the result "the formal content of the 6 EXACT IBM hits at
`peak_alpha = 1.500`". It is the same defect as the one ch21 calls the highest
referee risk, in a second place, unrecorded.

**This is the third instance this session of one pattern**: a defect recorded in
one location and not in its twin (r382 — a header listing a lemma the tree
lacked; r385 — an obstacle recorded that did not exist).

## The sharp reason, which is what this file proves

The two anchors are not equally repairable, and rationality is what separates
them.

* **`α_RH = 3/2` is rational.** So a reported decimal peak *can* equal it
  exactly, which means the comparison can be — and is — discharged by `rfl`.
  A `rfl` comparison consumes no measurement: the reported value was set equal
  to the target by definition. **A rational target admits a vacuous exact-match
  claim.**
* **`α_NP = φ + 1/4` is irrational.** So **no** reported decimal can equal it,
  ever. `ibm_peak_PNP = 1868/1000 ≠ φ + 1/4` is a theorem
  (`ibm_peak_PNP_ne_alpha_NP`), which means the only true statement available is
  a *bracket* — and the corpus's bracket `|1868/1000 − (φ+¼)| ≤ 10⁻⁴` has real
  content, since the actual gap is `3.4 × 10⁻⁵`. **An irrational target forces
  an informative claim.**

So the corpus contains both kinds at once: in
`IBMEmpiricalAlphaTableBridge` the **NP** comparison (E2) is a genuine bracket
while the **RH** comparison (E1) is `rfl`; and in
`CrossMillenniumDerivedConsequences` there is a *second* NP comparison which is
`rfl` because it compares two `def`s of `φ + 1/4` with each other rather than
with a decimal. Only the last of those three is flagged.

**The diagnostic this yields:** an "exact match" between a framework value and a
reported measurement is informative only if the framework value is irrational,
or if the two sides are independently constructed. Where the target is rational
and the reported value is a `def`, `rfl` is guaranteed in advance and the
theorem is decoration.

## What is NOT claimed

Not claimed: that any IBM measurement did or did not happen — nothing here
touches the experiment, only what the Lean statements can carry. Not claimed:
that `α_RH = 3/2` or `α_NP = φ + 1/4` is wrong; both are postulates and are
untouched. Not claimed: that the bracket (E2) establishes the framework —
agreeing to four decimals with one reported number is weak evidence, and ch21's
ledger already records the `143`-problem run behind these labels as a local
simulator execution of a classical formula. Not claimed: that
`ibm_peak_RH_eq_alpha_RH` should be deleted — `3/2 = 3/2` is true; what needs
repair is the docstring calling it the formal content of an empirical result,
and the ledger's silence about it.

No downgrade: nothing is renamed or withdrawn here.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-30.
-/
import PF.SigmaAbscissa_r212

set_option autoImplicit false

namespace PrincipiaTractalis.Empirical.AnchorInformativeness

open PrincipiaTractalis.SigmaAbscissa

/-! ## §1 — The RH target is rational; the NP target is not -/

/-- `α_RH = 3/2` is rational. A reported decimal can therefore equal it
exactly — which is what makes a `rfl` "exact match" possible there. -/
theorem alpha_RH_rational : ∃ q : ℚ, ((q : ℝ)) = 3 / 2 :=
  ⟨3 / 2, by norm_num⟩

/-- `α_NP = φ + 1/4` is irrational — reusing r212's result. No reported decimal
can equal it. -/
theorem alpha_NP_irrational : Irrational (Real.goldenRatio + 1 / 4) :=
  irrational_goldenRatio_add_quarter

/-! ## §2 — So the NP comparison is between distinct numbers

This is what gives the NP bracket content: it is an approximation claim, not an
identity waiting for `rfl`. -/

/-- **★★★ r395: the reported NP peak is NOT the framework value ★★★**

`1868/1000 ≠ φ + 1/4`, because the left side is rational and the right is not.
So no `rfl` can close the NP comparison against a decimal, and only a bracket
can be true. -/
theorem ibm_peak_PNP_ne_alpha_NP :
    (1868 / 1000 : ℝ) ≠ Real.goldenRatio + 1 / 4 := by
  intro h
  refine alpha_NP_irrational ⟨1868 / 1000, ?_⟩
  rw [← h]
  norm_num

/-- More generally: **no rational equals the NP target.** Every "exact match"
claim against a reported decimal is false there, so an honest statement must be
a bracket. -/
theorem no_rational_eq_alpha_NP (q : ℚ) :
    ((q : ℝ)) ≠ Real.goldenRatio + 1 / 4 := by
  intro h
  exact alpha_NP_irrational ⟨q, h⟩

/-! ## §3 — The diagnostic, stated

A rational target admits a vacuous exact-match claim; an irrational one does
not. The RH anchor sits on the first side, the NP bracket on the second. -/

/-- **★ r395: the asymmetry, bundled ★**

The RH target is rational (so `rfl` against a `def`'d decimal is available and
uninformative); the NP target is irrational and differs from the reported
decimal (so only an informative bracket is available). -/
theorem anchor_informativeness_asymmetry :
    (∃ q : ℚ, ((q : ℝ)) = 3 / 2)
      ∧ Irrational (Real.goldenRatio + 1 / 4)
      ∧ (1868 / 1000 : ℝ) ≠ Real.goldenRatio + 1 / 4 :=
  ⟨alpha_RH_rational, alpha_NP_irrational, ibm_peak_PNP_ne_alpha_NP⟩

end PrincipiaTractalis.Empirical.AnchorInformativeness

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Empirical.AnchorInformativeness.alpha_RH_rational
#print axioms PrincipiaTractalis.Empirical.AnchorInformativeness.alpha_NP_irrational
#print axioms PrincipiaTractalis.Empirical.AnchorInformativeness.ibm_peak_PNP_ne_alpha_NP
#print axioms PrincipiaTractalis.Empirical.AnchorInformativeness.no_rational_eq_alpha_NP
#print axioms PrincipiaTractalis.Empirical.AnchorInformativeness.anchor_informativeness_asymmetry

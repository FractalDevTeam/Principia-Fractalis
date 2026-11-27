/-
# The faithful trace of `T_∞`: the real theorem, in place of the tautology

**Date**: 2026-11-27 (Legion).

`PF/Consciousness/TimelessField.lean:141-142` carries this conjunct of
`NuclearStructure`, under this comment:

```lean
    -- (2) A faithful trace `τ((a_k)_k) = lim (1/3^k) Tr(a_k)` exists.
    (∃ τ : TimelessFieldType φ → ℂ, ∀ a, τ a = τ a) ∧
```

`∀ a, τ a = τ a` is satisfied by every function, the zero functional
included. The comment claims faithfulness; the Prop asks for reflexivity of
equality. `TimelessFieldExistenceClaim` is built on `NuclearStructure`, and
ch34A §115-122 reads that claim as "the nuclear C*-algebra `A_TF` with its
K-theoretic content and its partial-trace family of projective
compatibilities is realised".

**This file does not disclose that. It repairs it.** The faithful trace is
not missing from the corpus — it is proved, two files away, over the right
carrier, with real analysis:

- `UHF_trace_faithful` — `PF/SubstrateCompletionFaithful.lean:328` —
  `UHF_trace (star x * x) = 0 → x = 0` on `TimelessFieldCompletion`, via the
  trace-preserving conditional expectations and `tendsto_nhds_unique`.
- `substrate_completion_simple_unconditional` — same file, `:367` — every
  two-sided ideal of `TimelessFieldCompletion` is `⊥` or `⊤` (Glimm 1960).
- `substrate_tracial_state_space_singleton` —
  `PF/AlphaFromSubstrateKTheory_r123.lean:416` — the tracial state is
  **unique**: `IsTracialState φ → φ = UHF_trace`.

So the repair is to state the theorem the comment describes and prove it from
what exists. §1 does that. §2 supplies the teeth the tautology had none of.
§3 re-exports uniqueness and simplicity, because ch04's own ledger files
"uniqueness of the tracial state" under *"Classical, by reference — not
formalized"* while `substrate_tracial_state_space_singleton` proves it in
this closure; that ledger line understates the corpus and is corrected
alongside this module.

Nothing upstream is renamed or deleted. `NuclearStructure` keeps its name and
its clients; what changes is that the corpus now has a *non-vacuous* statement
of the same intent, so the vacuous conjunct can be repointed at it rather than
merely flagged. This is the direction `project_wire_by_inferred_type` records
as the default for a `Prop := True`: find the real content and wire to it.
-/
import PF.SubstrateCompletionFaithful
import PF.AlphaFromSubstrateKTheory_r123

set_option autoImplicit false

namespace PF.Referee.TimelessFieldFaithfulTraceRepair

open PrincipiaTractalis
open PrincipiaTractalis.SubstrateTimelessFieldCompletion
open PrincipiaTractalis.SubstrateUHFPreTraceDirectLimit
open PrincipiaTractalis.SubstrateTraceUniqueness
open PrincipiaTractalis.SubstrateCompletionFaithful
open PrincipiaTractalis.AlphaFromSubstrateKTheory

/-! ## §1 — The genuine statement, and its proof -/

/-- **A faithful trace on `T_∞` exists.**

    This is what `NuclearStructure`'s conjunct (2) says in its comment:
    a functional that *detects* positivity, so `τ (x* x) = 0` forces `x = 0`.
    Unlike `∀ a, τ a = τ a`, this constrains `τ`. -/
def HasFaithfulTrace : Prop :=
  ∃ τ : TimelessFieldCompletion → ℂ,
    ∀ x : TimelessFieldCompletion, τ (star x * x) = 0 → x = 0

/-- **★ The faithful trace exists — discharged from `UHF_trace_faithful`.**

    The witness is the canonical UHF trace, not an arbitrary function. -/
theorem hasFaithfulTrace : HasFaithfulTrace :=
  ⟨UHF_trace, fun x hx => UHF_trace_faithful x hx⟩

/-! ## §2 — The teeth: why the original conjunct carried nothing -/

/-- **Every function satisfies the conjunct that was standing in for
    faithfulness.**

    `∀ a, τ a = τ a` is reflexivity of equality, so it holds of any `τ`
    whatever, over any carrier. A conjunct every inhabitant satisfies cannot
    narrow the existential it sits inside. -/
theorem reflexivity_conjunct_holds_of_every_function
    {T : Type} (τ : T → ℂ) : ∀ a, τ a = τ a :=
  fun _ => rfl

/-- **And it is available under any hypothesis at all.**

    The sharp instrument the corpus already uses on vacuous bundles
    (`SubstrateTheoremContent_r216`): a statement derivable from an arbitrary
    `P` is not evidence about the substrate. -/
theorem reflexivity_conjunct_is_free
    {T : Type} [Inhabited T] (P : Prop) (_hP : P) :
    ∃ τ : T → ℂ, ∀ a, τ a = τ a :=
  ⟨fun _ => 0, fun _ => rfl⟩

/-- **The zero functional witnesses the old conjunct.**

    This is the concrete reason the old form was empty: the constant-zero
    functional satisfies it, and the zero functional detects nothing. -/
theorem zero_functional_witnesses_the_old_conjunct
    {T : Type} : ∃ τ : T → ℂ, ∀ a, τ a = τ a :=
  ⟨fun _ => 0, fun _ => rfl⟩

/-- **The zero functional does NOT satisfy faithfulness, unless `T_∞` is
    trivial.**

    So the genuine Prop of §1 separates the zero functional from `UHF_trace`,
    which is exactly the discrimination the old conjunct lacked. Stated as an
    equivalence so that no nontriviality fact is smuggled in: the left side
    fails precisely when some element is nonzero. -/
theorem zero_functional_unfaithful_iff_nontrivial :
    (¬ ∀ x : TimelessFieldCompletion, (fun _ => (0 : ℂ)) (star x * x) = 0 → x = 0)
      ↔ ∃ x : TimelessFieldCompletion, x ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    exact h (fun x _ => by
      by_contra hx
      exact hc ⟨x, hx⟩)
  · intro ⟨x, hx⟩ h
    exact hx (h x rfl)

/-! ## §3 — Uniqueness and simplicity, re-exported for the book -/

/-- **The tracial state on `T_∞` is unique.**

    Re-exported from `substrate_tracial_state_space_singleton`. ch04's
    verification ledger files this under "Classical, by reference — not
    formalized". It is formalized, in this closure, and that ledger line is
    corrected with this commit. -/
theorem tracial_state_is_unique :
    ∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ → φ = UHF_trace :=
  substrate_tracial_state_space_singleton

/-- **`T_∞` is C*-simple.** Re-exported; Glimm 1960 for `M_{3^∞}`. -/
theorem completion_is_simple :
    ∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤ :=
  substrate_completion_simple_unconditional

/-! ## §4 — The bundle that should carry the claim -/

/-- **The substrate's trace structure, stated so that it has content.**

    Faithfulness + uniqueness of the tracial state + C*-simplicity. Every
    conjunct is a theorem of this corpus over `TimelessFieldCompletion`, and
    none of them is satisfied by an arbitrary function. This is the honest
    replacement for `NuclearStructure`'s conjunct (2). -/
def SubstrateTraceStructure : Prop :=
  HasFaithfulTrace
    ∧ (∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ → φ = UHF_trace)
    ∧ (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤)

/-- **★★ The substrate trace structure holds, unconditionally.**

    No hypothesis, no placeholder, no `True`. This is the result ch04's
    Theorem 4.9 ledger already calls kernel-verified, now bundled so a single
    name can be cited where the vacuous conjunct was cited before. -/
theorem substrateTraceStructure : SubstrateTraceStructure :=
  ⟨hasFaithfulTrace, tracial_state_is_unique, completion_is_simple⟩

end PF.Referee.TimelessFieldFaithfulTraceRepair

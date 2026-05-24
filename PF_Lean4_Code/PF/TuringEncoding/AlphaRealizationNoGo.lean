/-
# Alpha-Realization No-Go: Concrete `alpha_of_class` ⇔ Deciding P vs NP

★ 2026-05-24 — formalizing the framework's own structural admission ★

## What this file is

The framework's `alpha_of_class : Set Language → ℝ` (in
`PF/TuringEncoding/Operators.lean`, line 178) is declared `opaque` —
deliberately so. The docstrings at `Operators.lean:213-228` and
`AlphaCanonical.lean:21-26` state that the opacity is **structurally
load-bearing**:

> "the path to genuinely retire the axiom requires either:
>  (a) defining `alpha_of_class` concretely (breaks the downstream P ≠ NP
>      chain since concrete-definition forces ClassP=ClassNP → equal α values),
>  (b) deriving the assignment from a rigorous SA reality criterion ..."

This file formalises the (a) horn as a **clean Lean theorem**: the mere
*existence* of any concrete realisation `f : Set Language → ℝ` with the
canonical pair `f ClassP = √2 ∧ f ClassNP = φ + 1/4` is **logically
equivalent** to `ClassP ≠ ClassNP` — i.e., to deciding P vs NP itself.

The forward direction is the framework's own admission: if such `f`
exists, then `f ClassP ≠ f ClassNP` (since `√2 ≠ φ + 1/4`), and so the
arguments must be distinct sets.

The backward direction is the classical construction: given
`ClassP ≠ ClassNP`, we **classically** case-split on set equality to
build `f` explicitly. This uses `Classical.choice` (via
`Classical.byCases` on the decidable propositions `S = ClassP` and
`S = ClassNP`) but no further axioms — and crucially **no project
axioms**.

## Why this matters

This is the formal **sharpness certificate** for the framework's
"1-named-hypothesis" architecture. The `PolylogEigenvalueConjecture`
hypothesis (`PF/TuringEncoding/Operators.lean:250`) cannot be replaced
by a concrete construction of `alpha_of_class` without first solving
P vs NP. The opacity of `alpha_of_class` is therefore not a
formalisation gap — it is **exactly as hard as the problem itself**.

The classical witness construction here also gives a free corollary:
**any** decidability assumption that distinguishes ClassP from ClassNP
already implies the witness — so the existential side of
`PolylogEigenvalueConjecture` (on this canonical pair) is itself
**equivalent** to P ≠ NP.

## What is NOT claimed

This file does **not** prove `ClassP ≠ ClassNP`. It proves
**equivalence**: the existential statement about `f` and the
class-distinctness statement are interchangeable.

It also does **not** retire the `PolylogEigenvalueConjecture`
hypothesis. On the contrary, it shows that any concrete discharge of
the existential half of that hypothesis would constitute a proof
of P ≠ NP.
-/

import PF.TuringEncoding.Operators
import PF.TuringEncoding.AlphaCanonical
import PF.IntervalArithmetic

namespace PrincipiaTractalis.TuringEncoding

open Classical

/-- **Meta-theorem (framework sharpness).** A concrete real-valued
    function on `Set Language` realising the canonical pair
    `f ClassP = √2 ∧ f ClassNP = φ + 1/4` **exists** if and only if
    `ClassP ≠ ClassNP` — i.e., if and only if P ≠ NP.

    Forward: any such `f` forces distinct outputs on `ClassP` and
    `ClassNP` (because `√2 ≠ φ + 1/4` by `phi_plus_quarter_gt_sqrt2`),
    hence the inputs must be distinct sets.

    Backward: assuming `ClassP ≠ ClassNP`, the classical case-split
    function
    ```
    f S := if S = ClassP then √2 else if S = ClassNP then φ + 1/4 else 0
    ```
    realises the pair. -/
theorem alpha_realization_canonical_pair_iff_classes_distinct :
    (∃ f : Set Language → ℝ,
        f ClassP = Real.sqrt 2 ∧ f ClassNP = phi + 1/4) ↔
      ClassP ≠ ClassNP := by
  constructor
  · -- (→) any realising `f` forces the classes apart.
    rintro ⟨f, hP, hNP⟩ heq
    -- If ClassP = ClassNP then `f ClassP = f ClassNP`, contradicting
    -- `√2 ≠ φ + 1/4`.
    have hf : f ClassP = f ClassNP := congrArg f heq
    rw [hP, hNP] at hf
    -- hf : Real.sqrt 2 = phi + 1/4, but phi+¼ > √2.
    linarith [phi_plus_quarter_gt_sqrt2]
  · -- (←) classical construction of a realising `f` given the
    -- classes are distinct.
    intro hne
    refine ⟨fun S => if S = ClassP then Real.sqrt 2
                     else if S = ClassNP then phi + 1/4 else 0, ?_, ?_⟩
    · -- f ClassP = √2: the first `if` fires by `rfl`.
      simp
    · -- f ClassNP = φ + 1/4: first `if` does NOT fire (ClassNP ≠ ClassP
      -- is symmetric of `hne`), second `if` does fire by `rfl`.
      have hne_sym : ClassNP ≠ ClassP := fun h => hne h.symm
      simp [hne_sym]

/-- **Consequence.** The *existential* half of
    `PolylogEigenvalueConjecture` — the assertion that *some* concrete
    `f : Set Language → ℝ` realises the canonical algebraic pair
    `((f ClassP)² = 2 ∧ 0 < f ClassP) ∧
     (16 (f ClassNP)² − 24 (f ClassNP) − 11 = 0 ∧ 0 < f ClassNP)` —
    is equivalent to `ClassP ≠ ClassNP`.

    This packages the algebraic content of the hypothesis at the
    existential level: any concrete witness for the algebraic system
    on the canonical pair must already separate ClassP from ClassNP,
    and conversely the classical witness construction realises the
    canonical pair on distinct sets. -/
theorem algebraic_realization_iff_classes_distinct :
    (∃ f : Set Language → ℝ,
        ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
        (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
         0 < f ClassNP)) ↔
      ClassP ≠ ClassNP := by
  constructor
  · -- (→) The algebraic pair pins `f ClassP = √2` and `f ClassNP = φ+¼`
    -- (via `algebraic_pair_to_value_assignment` in `AlphaCanonical`),
    -- whence the canonical-pair realisation theorem gives the conclusion.
    rintro ⟨f, halg⟩
    have ⟨hP, hNP⟩ := algebraic_pair_to_value_assignment halg
    exact alpha_realization_canonical_pair_iff_classes_distinct.mp ⟨f, hP, hNP⟩
  · -- (←) The classical witness from the canonical-pair theorem
    -- automatically satisfies the algebraic system (`canonical_alpha_algebraic_pair`).
    intro hne
    obtain ⟨f, hP, hNP⟩ :=
      alpha_realization_canonical_pair_iff_classes_distinct.mpr hne
    refine ⟨f, ?_, ?_⟩
    · rw [hP]; exact ⟨alpha_P_sq, alpha_P_pos⟩
    · rw [hNP]; exact ⟨alpha_NP_quadratic, alpha_NP_pos⟩

/-! ## Framework-sharpness corollary

The composite theorem below states the *contrapositive* meta-claim:
**no** axiom-free concrete construction of `alpha_of_class` realising
the canonical pair can exist without simultaneously proving P ≠ NP.
This is the precise sense in which the `PolylogEigenvalueConjecture`
hypothesis is **structurally minimal**: any further discharge of its
existential half is itself a proof of the underlying complexity-class
separation. -/

/-- **Sharpness certificate.** Discharging the existential half of
    `PolylogEigenvalueConjecture` on the canonical pair is *exactly*
    as hard as proving `ClassP ≠ ClassNP`.

    This is the precise formal sense in which `alpha_of_class` must
    remain `opaque` until P vs NP is settled: any concrete witness is
    a P-vs-NP solver in disguise. -/
theorem alpha_concrete_realization_implies_P_neq_NP
    (f : Set Language → ℝ)
    (hP : f ClassP = Real.sqrt 2) (hNP : f ClassNP = phi + 1/4) :
    ClassP ≠ ClassNP :=
  alpha_realization_canonical_pair_iff_classes_distinct.mp ⟨f, hP, hNP⟩

end PrincipiaTractalis.TuringEncoding

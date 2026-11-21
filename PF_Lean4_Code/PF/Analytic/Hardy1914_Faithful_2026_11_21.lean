/-
# Hardy 1914 and the Odlyzko first zero, faithfully stated

**2026-11-21.** Additive. Nothing in any existing file is renamed,
weakened or removed.

## The defect this repairs

`PF/Analytic/Hardy1914_NonemptyZetaOnLineZeros_Anchor.lean` carries two
theorems whose docstrings claim a conclusion their statements do not
contain. Its headline reads

> ★★★★★ SUBSTRATE-LEVEL DISCHARGE of atomic fact (b) … then the atomic
> fact `PositiveOnLineZetaZeroOrdinatesNonempty` follows at substrate
> level

and the theorem is

```
theorem hardy1914_anchor_yields_nonempty_substrate_implication
    (_h : Hardy1914_OnLineZetaZerosInfinite_Anchor) :
    Hardy1914_OnLineZetaZerosInfinite_Anchor := _h
```

`True → True`, by the identity. `PositiveOnLineZetaZeroOrdinatesNonempty`
never appears. The same holds for the Odlyzko twin, and
`nonempty_substrate_discharge_via_named_anchors` proves
`True ∧ True ∧ 0 < 14.134725141734693` — the only content being that a
decimal literal is positive.

That file's *scope* paragraphs are honest about all of this. Its theorem
names and its ★★★★★ framing are not, which is the failure mode the
2026-08-01 `Prop := True` audit named: the docstrings were honest and the
names were not.

## What was already right, and is reused here

`PF/Analytic/HPPositiveViaHardyAndCountability_r281.lean` had already
done the real work: `Hardy1914_AtomicFact` is a genuine existential,
`hardy1914_atomicFact_eq_nonempty` proves it equivalent to the
framework's atomic fact, and `hp_positive_via_hardy_and_countability`
reduces HP-positivity to it. **The faithful statement existed; only the
`True` anchor layer sitting on top of it did not connect.** This file
connects them. (r281 imports the anchor file, so this must be a new
module rather than an edit, or the import graph would cycle.)

## What is added

Hardy's theorem is **stronger** than the atomic fact the framework needs
— infinitely many on-line zeros, where one suffices — so the faithful
statement implies the atomic fact through `Set.Infinite.nonempty`. That
is the real content the anchor file's prose was describing:

  `Hardy1914_Faithful  →  PositiveOnLineZetaZeroOrdinatesNonempty`
  `Hardy1914_Faithful  →  PF_T3SymIsHilbertPolyaOperator_Positive`  (via r281)

and likewise for the computational record, stated as what the
computation actually establishes — a zero *in an interval* — rather than
as an equality at a truncated decimal, which would be false.

## Scope, stated plainly

`Hardy1914_Faithful` and `Odlyzko_FirstZero_Faithful` are **hypotheses,
undischarged**. Hardy 1914 is a referee-checked theorem of 110 years'
standing and the first-zero computation has been independently
reproduced (Gourdon 2004, Platt 2017 by rigorous interval arithmetic),
but neither is formalised in mathlib at this pin and neither is proved
here. **Nothing here proves the Riemann Hypothesis**, and nothing here
closes any Clay problem. What changes is that the framework's reduction
now rests on faithful statements of those results instead of on `True`.
-/

import PF.Analytic.Hardy1914_NonemptyZetaOnLineZeros_Anchor
import PF.Analytic.HPPositiveViaHardyAndCountability_r281

namespace PrincipiaTractalis.Hardy1914_Faithful_2026_11_21

open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HilbertPolyaPositiveImageRigidity
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open PrincipiaTractalis.HPPositiveViaHardyAndCountability
open PrincipiaTractalis.Hardy1914_NonemptyZetaOnLineZeros_Anchor

/-! ## §1 — Hardy 1914, faithfully

G. H. Hardy, *Sur les zéros de la fonction ζ(s) de Riemann*, C. R. Acad.
Sci. Paris **158** (1914), 1012–1014; expanded as *On the zeros of the
Riemann zeta-function*, Proc. London Math. Soc. (2) **14** (1915),
269–277.

What Hardy proved: `ζ(1/2 + it) = 0` for infinitely many real `t`, hence
for infinitely many positive `t`. In the corpus's own vocabulary that is
exactly `PositiveOnLineZetaZeroOrdinates.Infinite`, so the statement
needs no new definitions — only the right one. -/

/-- **Hardy 1914, as a statement rather than a marker.** Infinitely many
    positive ordinates `t` with `ζ(1/2 + it) = 0`.

    Undischarged: this is a hypothesis naming a published theorem, and
    the theorem is not formalised at this mathlib pin. The difference
    from `Hardy1914_OnLineZetaZerosInfinite_Anchor` is that this Prop is
    *about* ζ. -/
def Hardy1914_Faithful : Prop :=
  PositiveOnLineZetaZeroOrdinates.Infinite

/-- **★ Hardy 1914 yields the framework's atomic fact.**

    This is the implication the anchor file's docstrings claimed and its
    theorems did not state. It is true for a reason — Hardy gives
    *infinitely many* zeros where the atomic fact needs *one* — and the
    reason is `Set.Infinite.nonempty`. -/
theorem hardy1914_faithful_yields_nonempty (h : Hardy1914_Faithful) :
    PositiveOnLineZetaZeroOrdinatesNonempty :=
  h.nonempty

/-- Hardy's statement also gives r281's existential form directly. -/
theorem hardy1914_faithful_yields_atomicFact (h : Hardy1914_Faithful) :
    Hardy1914_AtomicFact :=
  hardy1914_atomicFact_eq_nonempty.mpr h.nonempty

/-- **★★ Hardy 1914 yields HP-positivity**, composing with r281's
    countability discharge.

    So the framework's HP-positive reduction now rests on a faithful
    statement of Hardy's theorem. It does **not** prove RH: the
    hypothesis is undischarged, and HP-positivity is not RH. -/
theorem hardy1914_faithful_yields_hp_positive (h : Hardy1914_Faithful) :
    PF_T3SymIsHilbertPolyaOperator_Positive :=
  hp_positive_via_hardy_and_countability (hardy1914_faithful_yields_atomicFact h)

/-! ## §2 — The computational record, faithfully

A. M. Odlyzko's high-precision computations, independently reproduced by
Gourdon (2004) and verified by Platt (2017) with rigorous interval
arithmetic, place the first positive ordinate at

  `t₁ = 14.134725141734693790457251983562470270784257115699243175685…`

**The statement must be an interval, not an equality.** The anchor file
defines `riemannFirstZeroOrdinate_substrate := 14.134725141734693`, a
truncation — and `riemannZeta ⟨1/2, 14.134725141734693⟩ = 0` is *false*,
since the truncated decimal is not the zero. What the computation
establishes is that a zero lies in a narrow interval around it, which is
what is stated here. -/

/-- **The first-zero computation, as a statement rather than a marker.**
    There is an on-line ζ-zero with ordinate strictly between
    `14.1347251417` and `14.1347251418`.

    Undischarged. Stated as an interval because the point statement at
    the truncated decimal would be false. -/
def Odlyzko_FirstZero_Faithful : Prop :=
  ∃ t : ℝ, 14.1347251417 < t ∧ t < 14.1347251418 ∧
    riemannZeta ⟨1/2, t⟩ = 0

/-- **★ The first-zero computation yields the framework's atomic fact.**
    A zero in that interval is a positive on-line zero, because the
    interval lies in the positive reals. -/
theorem odlyzko_faithful_yields_nonempty (h : Odlyzko_FirstZero_Faithful) :
    PositiveOnLineZetaZeroOrdinatesNonempty := by
  obtain ⟨t, hlo, _hhi, hz⟩ := h
  exact ⟨t, by norm_num at hlo ⊢; linarith, hz⟩

/-- The computational record likewise yields HP-positivity via r281. -/
theorem odlyzko_faithful_yields_hp_positive (h : Odlyzko_FirstZero_Faithful) :
    PF_T3SymIsHilbertPolyaOperator_Positive :=
  hp_positive_via_hardy_and_countability
    (hardy1914_atomicFact_eq_nonempty.mpr (odlyzko_faithful_yields_nonempty h))

/-- Either published result suffices — the disjunction is enough. -/
theorem published_record_yields_hp_positive
    (h : Hardy1914_Faithful ∨ Odlyzko_FirstZero_Faithful) :
    PF_T3SymIsHilbertPolyaOperator_Positive :=
  h.elim hardy1914_faithful_yields_hp_positive odlyzko_faithful_yields_hp_positive

/-! ## §3 — What the two `True` anchors carry, in the kernel

The repair above is additive, so the original anchors remain. This
section records what they are, so that a referee who greps the anchor
file's ★★★★★ headline finds the measurement next to it rather than only
in prose. Same instrument as
`PF/Referee/SixAxisPhase1NamedAnchors_MasterCapstone_2026_06_19.lean` §3. -/

/-- Both named anchors are `True`. -/
theorem named_anchors_are_true :
    (Hardy1914_OnLineZetaZerosInfinite_Anchor ↔ True) ∧
    (Riemann_FirstZero_Verified_Anchor ↔ True) :=
  ⟨⟨fun _ => trivial, fun _ => trivial⟩,
   ⟨fun _ => trivial, fun _ => trivial⟩⟩

/-- **The two anchors are the same Prop.** Hardy's 1914 existence
    theorem and Odlyzko's 1992 computation are different results by
    different methods seventy-eight years apart, and these two markers
    are provably equal — because both are `True`.

    A citation registry needs distinct inhabitants; a family of
    `Prop := True` has exactly one. This is why the anchor pair cannot
    carry the distinction its docstrings draw between the two sources,
    and why §1 and §2 state them separately. -/
theorem named_anchors_are_not_distinct :
    Hardy1914_OnLineZetaZerosInfinite_Anchor = Riemann_FirstZero_Verified_Anchor :=
  rfl

/-- **The anchor file's two "substrate-implication discharge" theorems
    are the identity.** Their conclusion is their own hypothesis, so
    neither mentions — let alone yields — the atomic fact its docstring
    names. §1 and §2 supply the implications that do. -/
theorem anchor_implications_are_identities :
    (Hardy1914_OnLineZetaZerosInfinite_Anchor
      ↔ Hardy1914_OnLineZetaZerosInfinite_Anchor) ∧
    (Riemann_FirstZero_Verified_Anchor ↔ Riemann_FirstZero_Verified_Anchor) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- The faithful statements are strictly more informative than the
    markers: each *implies* the atomic fact, which `True` cannot. -/
theorem faithful_statements_are_not_markers :
    (Hardy1914_Faithful → PositiveOnLineZetaZeroOrdinatesNonempty) ∧
    (Odlyzko_FirstZero_Faithful → PositiveOnLineZetaZeroOrdinatesNonempty) :=
  ⟨hardy1914_faithful_yields_nonempty, odlyzko_faithful_yields_nonempty⟩

#print axioms hardy1914_faithful_yields_nonempty
#print axioms hardy1914_faithful_yields_atomicFact
#print axioms hardy1914_faithful_yields_hp_positive
#print axioms odlyzko_faithful_yields_nonempty
#print axioms odlyzko_faithful_yields_hp_positive
#print axioms published_record_yields_hp_positive
#print axioms named_anchors_are_true
#print axioms named_anchors_are_not_distinct
#print axioms anchor_implications_are_identities
#print axioms faithful_statements_are_not_markers

end PrincipiaTractalis.Hardy1914_Faithful_2026_11_21

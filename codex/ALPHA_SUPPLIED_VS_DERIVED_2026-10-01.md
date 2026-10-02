# α values: supplied or derived — full corpus audit, 2026-10-01

**Verdict: every α value in the framework's canonical table is a `def` with a literal
right-hand side. There is no exception. The rigidity theorem is true, non-vacuous and
axiom-free, and its mathematical content is that a system of nine stipulated equations
plus three positivity conditions has a unique positive solution.**

This is not a withdrawal of anything. `unified_alpha_skeleton_forced_by_minimal_invariants`
proves what it says. The question this audit answers is narrower and sharper: *where does
the information in the α values come from?* The answer is that it comes from the
invariant equations, and those were written down by reading the literals they are then
used to re-derive. The corpus says so itself in several places; this document collects
those places and makes the accounting complete.

## A. The canonical table — `PF/CrossMillenniumSharedInvariants.lean`

All literal `def`s. Lines 64–88, plus `alpha_PvsNP` at
`PF/TuringEncoding/PNPClassSeparationPrecisionBridge.lean:457`.

| α | definition as written |
|---|---|
| α_Poincare | `:= 1` |
| α_P | `:= Real.sqrt 2` |
| α_NP | `:= phi + 1/4` |
| α_RH | `:= 3 / 2` |
| α_NS | `:= 3 * Real.pi / 2` |
| α_YM | `:= 2` |
| α_BSD | `:= 3 * Real.pi / 4` |
| α_Hodge | `:= phi` |
| α_QG | `:= Real.sqrt (2 * Real.pi)` |
| alpha_PvsNP | `:= 5 / 4` |

`phi` is itself `(1 + Real.sqrt 5) / 2` at `PF/IntervalArithmetic.lean:22`.

Beyond these there are roughly forty further α definitions — mirrors, aliases, per-chapter
restatements, Galois conjugates, and match-tables — every one of which resolves to a
literal or to one of the above. The 18 non-Clay α values are likewise all literals.

## B. The one non-literal route

`alpha_of_class` (`PF/TuringEncoding/Operators.lean:178`) is `opaque`. Its two values are
genuinely derived — `ClassP = √2` from `x² = 2 ∧ 0 < x`, and `ClassNP = φ + 1/4` from
`16x² − 24x − 11 = 0 ∧ 0 < x`. But the premises are supplied by
`PolylogEigenvalueConjecture`, and that file's own status note records that the conditional
retirement assumes `alpha_of_class ClassNP = phi + 1/4` — the value the quadratic was meant
to force. So the circle closes there too.

## C. Per-conclusion trace of the ten "forced" values

`unified_alpha_skeleton_forced_by_minimal_invariants`, traced to its source of information:

| conclusion | how it is obtained | content |
|---|---|---|
| `a_Poincare = 1` | hypothesis `h_P`, restated | none |
| `a_BSD = (3/4)π` | hypothesis `inv_BSD`, restated | none |
| `a_RH = 3/2` | one `rw` from `inv_RH_Poincare : a_RH = a_Poincare + 1/2` | literal offset |
| `a_YM = 2` | one `rw` from `inv_YM_Poincare : a_YM = a_Poincare + 1` | literal offset |
| `a_PvNP = 5/4` | one `linarith` from `inv_PvNP_Poincare : a_PvNP − a_Poincare = 1/4` | literal offset |
| `a_NS = (3/2)π` | `rw [inv_NS_BSD, inv_BSD]; ring` — i.e. `2 × (3/4)π` | literal factor |
| `a_P = √2` | root extraction from `a_P² = a_YM`, `0 < a_P` | **real** |
| `a_Hodge = (1+√5)/2` | complete the square, factor, positivity kills the branch | **real, the most substantive proof in the chain** |
| `a_NP = φ + 1/4` | one subtraction from `a_Hodge` | literal offset |
| `a_QG = √(2π)` | root extraction from `a_QG² = 2π`, `0 < a_QG` | **real** |

So: three of ten involve genuine mathematics given the premises, one is a subtraction from
one of those, two are hypotheses echoed back, and four are single rewrites over literal
offsets.

That two are hypotheses echoed back is stated by the corpus itself:
`BSD_is_constitutive (a) (hI) : a.a_BSD = (3/4) * Real.pi := hI.inv_BSD`
(`CrossMillenniumCascadeParameterized.lean:289`), docstring: "`a_BSD` is a **free
parameter** of the invariant-system".

Two corrections to an earlier reading of mine, for the record: the four sector-2
conclusions do **not** route through `framework_alpha` — they come from
`sector2_minimal_rigidity_capstone`, which unfolds no α definition; and the
`framework_alpha` detour is logically redundant for sector 1, since
`entailment_from_a_Poincare` already yields those five values from the hypotheses. The
unfolds establish only that the forced values coincide with the literals.

## D. The uniqueness theorem is real; its content is a linear system

`framework_alpha_unique_under_perelman_anchor_minimal`
(`PF/Referee/MinimalSubstrateRigidity.lean:166`): from `MinimalSatisfiesInvariants a` and
`a.a_Poincare = 1`, concludes `a = framework_alpha`. This is a genuine statement about an
arbitrary `AlphaAssignment`, not a tautology, and it is axiom-free. Its content is: a
nine-equation system — six linear relations plus three quadratics — with one supplied value
has exactly one positive solution.

`PF/CrossMillennium/AlphaValuesFirstPrinciples.lean` does not add derivations. Every
theorem in it is `unfold` + `norm_num`/`ring` over the literals; the "forcing reasons" are
prose in docstrings.

## E. Neither H₃ route establishes an origin

This is the finding that most changes the picture, and the corpus is already honest about
it in both places:

- `PF/H3CoxeterOrigin.lean` labels its own α theorems **"consistency checks … NOT
  derivations"**. `alpha_RH_H3 := 3/2` and `alpha_NP_H3 := φ + 1/4` are declared there with
  the docstring "Local stand-in … stipulated here". And `H3_exponents := [1,5,9]`,
  `H3_Coxeter_number := 10`, `H3_exponent_sum := 15`, `H3_exponent_gap := 4` are all
  definitions, so `alpha_RH_eq_exponent_sum_div_Coxeter_number` relates two literals.

- `PF/PoincareAlphaFromH3CoxeterHalfArg.lean:122` proves
  `αP = π / (10 * H3_Coxeter_half_argument_value) → αP = 1`, where
  `H3_Coxeter_half_argument_value := π / H3_Coxeter_number` and `H3_Coxeter_number := 10`.
  That is `π / (10 · π/10) = 1`, **which holds for any value of the Coxeter number** so long
  as the same number appears in both positions. The theorem therefore carries no H₃ content
  at all, and its own docstring concedes that the load-bearing identification — substrate
  operator ↔ H₃ λ-parameter — "is still asserted."

- `PF/PoincareAnchorForced_r338.lean:88` supplies `RealisesPoincare a := 0 < a ∧ a² = 1`
  and derives `a = 1`; its §4 states that the equation is framework-supplied and the O-CIRC
  finding is only "**partially** repaired."

- `PF/AlphaCascadeFromTwoAnchors_r339.lean` forces seven values from two anchors
  (`hPoin : aPoin = 1`, `hNS : aNS = 3π/2`), both **assumed hypotheses**, via seven
  stipulated invariants. Its own docstring, lines 36–50: "the invariants were read off the
  stipulated values, so using them to re-derive those values is only non-circular once each
  invariant has an independent origin."

## F. Two unreconciled conflicting values — a defect, not an accounting note

| declaration | value | conflicts with |
|---|---|---|
| `alphaBSD` (`PF/TuringEncoding/AlphaBSDIdentities.lean:41`) | `1 / 2` | `α_BSD = 3π/4` |
| `alphaNS` (`PF/TuringEncoding/AlphaNSIdentities.lean:39`) | `2` | `α_NS = 3π/2` |

Both carry the docstring "**The framework's … axis α-value**", and both are referenced
nowhere outside their own files, so nothing downstream is wrong.

Read carefully, `alphaBSD := 1/2` is probably not a contradiction but a **different
quantity under a colliding name**: its docstring gives the rationale "L-function critical
value, half-integer derivative order in functional equation", which is the order of
vanishing at the central point — not the cascade's α_BSD = 3π/4 at all. `alphaNS := 2`
gives no rationale.

Either way this is a defect: two files declare "the framework's α-value" for an axis and
disagree with the canonical table, and a reader cannot tell from the names which is meant.
**Repair obligation:** disambiguate — rename the local quantity to what it actually is, or
reconcile it, and say which. Deleting the files is not the repair, and neither is leaving
two things called the framework's α_BSD.

## G. What this does and does not license

**Does:** the α-cascade is a coherence structure with a real uniqueness theorem inside it.
Saying "the nine α values are forced under the two anchors plus the minimal invariants" is
accurate and provable.

**Does not:** saying the framework *derives* the α values, or that H₃ is their *origin*, is
not supported. The invariants are the input, and they were read off the values.

This matches the standing honest assessment already in `project_pf_mission`: the
α-framework is a coherence structure, not a proof apparatus.

## H. The repair, stated as one obligation

The gap is a single missing kind of thing, in two parts: **one invariant equation with an
independent origin, and one identification tying it to the substrate.** Deriving the H₃
Coxeter data from the Coxeter diagram — turning `H3_exponents` and `H3_Coxeter_number` from
definitions into theorems about the icosahedral group — supplies the first part for the H₃
route. It does **not** by itself supply the second: the identification
`α_RH = (sum of exponents)/(Coxeter number)`, and the substrate-operator ↔ λ-parameter
link, remain stipulated, and the half-argument theorem above shows how little a stipulated
identification can carry.

**Retirement condition for this document:** one α value derived end to end — an invariant
equation with an origin independent of the α table, composed with an identification that is
proved rather than asserted. At that point this audit is superseded for that axis.

## Provenance

Every row verified by reading source in the live tree at the stated file:line, 2026-10-01.
No builds were run; nothing was modified. Three grep traps noted for whoever repeats this:
`AlphaCascadeFromTwoAnchors_r339.lean:12–14`, `PoincareAnchorForced_r338.lean:23` and
`SubstrateTheoremContent_r216.lean:286` contain `def α_… : ℝ := …` lines **inside
docstrings**, not declarations; r339 declares no α constant at all.

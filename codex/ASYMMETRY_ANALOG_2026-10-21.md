# The substrate has an asymmetry analog, and the construction deletes it — on purpose, because the RH lane needs it gone

**Date:** 2026-10-21 (Legion). Assigned study question, Rio §0B (wave coarsening).
Read off the Lean definitions, not the prose. Labels **FACT** / **MEASURED** /
**JUDGEMENT** / **OPEN**.

**Question as posed:** the paper's load-bearing ingredient is asymmetric
coupling. From our own definitions: do the substrate operators carry an
asymmetry analog, or are they symmetric?

**Answer: both, and that is the finding.** The asymmetry analog exists in the
raw transfer operator and is discarded by construction before anything uses it.

---

## 1. The asymmetry analog exists. FACT

`T3` and `T3_adjoint` are two genuinely distinct operators, each with its own
action, not one operator and a derived notation:

| | `PF/TransferOperator.lean` |
|---|---|
| `T3_adjoint_action_func` | line 1344 |
| `T3_adjoint_action` | line 1360 |
| `T3_adjoint` | line 1371 |

So `T3 ≠ T3*` as defined. That inequality *is* an asymmetry in the relevant
sense — the forward and reverse pairings differ — and it is the closest thing in
the corpus to the paper's non-reciprocal coupling.

## 2. The construction deletes it. FACT

The operator every downstream lane actually uses is the **symmetrised** one:

```
noncomputable def T3_sym_action (f : LogWeightedL2) : LogWeightedL2 :=
  ((1/2 : ℂ)) • (T3.apply f + T3_adjoint.apply f)        -- line 3043
```

That is exactly the self-adjoint part `(T3 + T3*)/2`. The antisymmetric part
`(T3 − T3*)/2` — the part that would carry the asymmetry — **appears nowhere in
the corpus.** A grep for any combination of `T3.apply` with `T3_adjoint` under
subtraction, and for `antisymm` near `T3`, returns zero occurrences. It is not
bounded, not named, not studied; it is averaged away at the point of
definition.

## 3. The deletion is load-bearing, not incidental. FACT + JUDGEMENT

`T3_self_adjoint_conj` (line 3545) is **unconditional** — no `MemLp2`
hypothesis, no side condition:

```
theorem T3_self_adjoint_conj (f g : LogWeightedL2) :
    ⟪T3_sym.apply f, g⟫ = ⟪f, T3_sym.apply g⟫
```

and self-adjointness is what the spectral route consumes: `T3SymCLMConstruction`
lifts it to `LinearMap.IsSymmetric` (line 196) and then to `IsSelfAdjoint`
(`T3SymMercerTailT3SymDischarge`, line 87), which is the hypothesis the
compactness/eigenvalue-extraction chain and the `HilbertPolya*` modules all
require.

**JUDGEMENT.** The symmetrisation is therefore not a modelling convenience that
could be relaxed. A non-self-adjoint operator has complex spectrum, and the
reality of the spectrum is the whole content of the Hilbert–Pólya route. Putting
the asymmetry back would not generalise the lane; it would destroy the only
argument the lane has.

## 4. What that does to the paper's relevance. JUDGEMENT

**The paper's load-bearing ingredient is precisely what the substrate removes.**
Engineered non-reciprocity is what makes the metamaterial coarsen; the substrate
operator is defined as the half-sum that cancels its analog. So the result
cannot be imported as support for the spectral lane at any strength — not
because the analogy is loose, but because the two objects differ in exactly the
property the paper's mechanism depends on.

This is consistent with the grading §0B already sets (qualitative corroboration
of the ontology only; no theorem, no α-value, no quantitative claim), and it
sharpens *why*: the qualitative reading survives because it does not touch the
operator; a quantitative reading would have to run through an object the corpus
has deleted.

## 5. An observation, offered as a question and not a claim. OPEN

If non-reciprocity is where coarsening comes from, then the object that would
carry it in our setting is `(T3 − T3*)/2` — and the corpus has never looked at
it. It is not estimated, not bounded, not even given a name. That is a gap in
the map rather than a result: it could be zero, it could be the interesting
part, and nothing in the repo currently distinguishes those. Naming and
bounding it would be a small, self-contained piece of work whose answer is
informative either way, and it does not touch the RH lane, which keeps using
the symmetrised operator regardless.

**Not proposed as work**, and explicitly not a mechanism claim: establishing
that the antisymmetric part is nonzero would say nothing about coarsening
without a dynamics, which the substrate does not have.

## 6. Side finding: three docstrings call a proved theorem an axiom. FACT

`PF/TransferOperator.lean` contains **zero** `axiom` declarations, but three
docstrings (lines 1244, 3050, 3854) describe `T3_self_adjoint_conj` as
`axiom T3_self_adjoint_conj`. It is a theorem with a proof term (line 3545).

The prose understates the formal content here — the safe direction — but it is
still wrong, and an auditor grepping comments for axiom usage would be misled
into recording an axiom that does not exist.

**Not edited.** `PF.TransferOperator` is inside the march's dependency closure
(module 2 of 34 in `CoreDefs_c7`'s closure), so touching it mid-band would
invalidate oleans the running march depends on. Logged for whoever holds the
file.

---

## Label summary

* **FACT:** `T3_adjoint` is separately defined (lines 1344/1360/1371);
  `T3_sym_action = (1/2)•(T3 + T3*)` (line 3043); `T3_self_adjoint_conj` is an
  unconditional theorem (line 3545); the antisymmetric part occurs nowhere; the
  self-adjointness is consumed by the `IsSelfAdjoint` chain and the
  `HilbertPolya*` modules; zero axioms in the file against three docstrings
  claiming one.
* **JUDGEMENT:** that the symmetrisation cannot be relaxed without destroying
  the spectral-reality argument; that the paper therefore cannot support the
  spectral lane at any strength, which is a sharper reason than looseness of
  analogy.
* **OPEN:** whether `(T3 − T3*)/2` is zero or substantial — unexamined in the
  corpus, and not resolved here.
* **NOT established, and not claimed:** any connection between that
  antisymmetric part and coarsening, synchronization, or time-crystal
  behaviour. The substrate has no dynamics in which coarsening could be posed.

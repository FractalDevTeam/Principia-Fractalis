# The 2026-08-24 "no KMS path" verdict: inventory correct, impossibility overreaching

Legion, 2026-10-28, on Pablo's instruction to double-check the KMS build against
the corpus with no assumptions. This is a correction to prior adjudication, so
it is written with the measurements in front of the conclusion.

## The prior adjudication

`codex/PF_TRANSCENDENTAL_CARRIER_AUDIT_2026-08-24.md` states, at line 92:

> **KMS states** on `T_∞ = 3^∞` | r113's `substrate_UHF_trace_unique` forbids
> nontrivial tracial states; a KMS state at inverse temperature β ≠ 0 would
> induce a modular automorphism group and hence a distinct tracial state on the
> fixed-point subalgebra, contradiction. **No KMS enrichment path exists on the
> current substrate.**

and at line 263:

> **Verdict.** No modular / KMS / crossed-product π-carrier exists in the
> corpus, and r113 forbids the tracial route. … Enriching this layer would
> require substantial new infrastructure and would exit the current substrate.

The audit labels the supporting reasoning **"(informal argument)"** at line 245.
This note takes that label at its word.

## What the audit got right, and it matters

**The inventory claim was correct, and stayed correct for two more months.**
Measured independently on 2026-10-28, before any of r363–r369 existed: `KMS` was
**0 files in PF and 0 files in mathlib**; Tomita–Takesaki modular automorphism
groups, **0**; GNS construction, **0** (the apparent grep hits are substrings of
"signs"/"assigns" plus `SobolevInequality`'s Gagliardo–Nirenberg–Sobolev, an
unrelated GNS); `IsFactor`, **0** (substrings of "satisfactory"); `Connes`, **0**.
`VonNeumannAlgebra H` exists as a structure with essentially no theory. The
audit's "substantial new infrastructure" estimate was also right — see
`codex/TOE_GATE_PRICED_2026-10-28.md`.

## Where the conclusion overreaches

**r113's hypothesis is traciality, and a KMS state at β ≠ 0 does not satisfy it.**
Measured from the source (`PF/SubstrateTraceUniqueness.lean:164`):

```
structure IsTracialState (φ : TimelessFieldCompletion → ℂ) : Prop where
  continuous ; add ; smul
  tracial : ∀ x y, φ (x * y) = φ (y * x)
  unital  : φ 1 = 1
```

and `substrate_UHF_trace_unique (φ) (hφ : IsTracialState φ) (x) : φ x = UHF_trace x`
(`:239`). The theorem is a statement **about tracial states only**. The KMS
condition is `ω(ab) = ω(b · σ_{iβ}(a))`, which reduces to `ω(ab) = ω(ba)`
exactly when the modular automorphism is trivial — that is, at β = 0. For
β ≠ 0 a KMS state is **not tracial**, so r113 does not reach it. r113 is not
contradicted by such a state; it simply says nothing about it.

**The bridging step does not close.** The argument's move is that a modular
automorphism group yields "a distinct tracial state **on the fixed-point
subalgebra**". But r113 quantifies over tracial states on *all* of
`TimelessFieldCompletion`. A trace on a proper subalgebra is not an instance of
r113's hypothesis, so no contradiction is derived. The inference needs a step
from "trace on the fixed-point subalgebra" to "tracial state on `T_∞`", and that
step is neither stated nor available.

**Uniqueness of the tracial state is routine for UHF and coexists with many
non-tracial states.** That a UHF algebra has exactly one tracial state is
standard; it places no restriction on its non-tracial states, of which there are
many (product states with non-uniform weights). Those are the classical source
of non-tracial KMS states on `M_{n^∞}`. Nothing in r113 touches them.

**A von Neumann completion is not a prerequisite.** The audit notes at :252
that "no proper von Neumann completion of `T_∞` is constructed in the corpus".
True, and irrelevant to the KMS *condition*, which is stated for a C\*-dynamical
system — `TimelessFieldCompletion` carries a `CStarAlgebra` instance
(`instCStarAlgebraTimelessFieldCompletion`, r54–r59). Tomita–Takesaki modular
theory would need the GNS von Neumann algebra; the KMS condition itself does not.

## This is the failure mode already on the project's record

The corpus already carries the rule this is an instance of: **never dress "the
construction does not do X" as "it CANNOT"; an impossibility needs its own
theorem.** The audit's inventory finding — the corpus contains no KMS carrier —
was measured and correct. The impossibility finding — no KMS path *exists* — was
inferred from an informal argument and is not supported by r113.

**Nothing here downgrades r113.** `substrate_UHF_trace_unique` is kernel-clean
and, as of 2026-10-28, independently reproduced off Acer (3266 jobs, 0 errors,
0 `sorryAx`; see `codex/status/legion.md`). What is narrowed is a *corollary
someone drew from it*, not the theorem.

## Consequence for gate (A)

`THE MAP` §5(A) asks for a dynamics / KMS state on `T_∞` whose spectral data
forces the dictionary. The 2026-08-24 verdict would have closed that line as
impossible. On measurement it is **open**, and r363–r366 now build the
finite-level KMS pair (identity, state, `exp(-βH)`, imaginary time) with every
declaration on the three-axiom bar — none of which contradicts r113, because
none of those functionals is tracial except at β = 0, where r363's
`modularAut_of_scalar` independently confirms the dynamics is trivial.

The live obstruction is therefore **not** r113. It is the one r369 found: the
strong tower condition `embed(X k) = X (k+1)` forces every weight to be scalar,
hence tracial, hence trivial. That is a real obstruction to *that* condition,
with a machine-checked proof, and the product-type family is the stated repair.

## What should change in the record

The line-92 cell and the line-263 verdict should be narrowed from "no KMS path
exists" to "no KMS carrier exists in the corpus, and r113 does not forbid one".
**Amending the audit is Pablo's call, not mine** — this note records the
measurement and the reasoning; it does not edit the audit.

## One caution against my own conclusion

I am confident about the scope of r113 because its hypothesis is explicit in the
source. I am *less* able to certify, from inside this corpus, that a non-tracial
KMS state on this particular `T_∞` can actually be constructed — that is the
work r369's repair begins, and it is not finished. The claim made here is the
narrow one: **the cited obstruction does not apply.** That is different from
"the construction succeeds", and the difference should be preserved.

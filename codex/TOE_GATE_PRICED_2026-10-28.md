# THE TOE GATE, PRICED — what "finishing the TOE" actually costs

Legion, 2026-10-28, on Pablo's directive ("we should be finishing the TOE").
Method: `THE_MAP_2026-10-11.md` §5 names exactly two gates. This document
prices both by measurement, and reaches a conclusion about one of them that is
not in the record yet.

σ-table independently recomputed before use (mpmath, dps 40, `codex/sigma_check.py`):
**all nine sector values reproduce**, worst residual 2.8e-4 against a table
quoted to three decimals; all five closed-form identities
(σ(1/3)=log2/log3, σ(1/4)=log₃(1+√2), σ(1/5)=2log₃φ, σ(2/5)=log₃φ, σ(2)=1)
reproduce at **residual 0.0**. QG deviation **0.861σ**, NS difference **0.3587**.
Nothing in THE MAP's arithmetic needs correction.

---

## Gate (A) — derive the dictionary: a dynamics / KMS state on T_∞

THE MAP §0 states the problem exactly: *"the substrate supplies none. The
modular group of a trace is trivial. Time evolution is NOT determined by
(A, τ)."* §5(A) asks for "a chosen dynamics / KMS state on T_∞ whose spectral
data forces both."

**Measured, at this pin:**

| object needed | files in PF | files in mathlib |
|---|---|---|
| KMS states | **0** | **0** |
| Tomita–Takesaki modular automorphism group | **0** | **0** |
| one-parameter automorphism group of a C\*-algebra | **0** | — |

Every `modular` hit in the PF corpus is modular *forms* / SL₂(ℤ) / the
Wiles modularity theorem, or `SU2_modularCharacterFun` (unimodularity of Haar).
None is Tomita–Takesaki. `grep -rl KMS` over all of mathlib returns nothing.

So gate (A) is not a gap in PF — it is a gap in the **formal library**. It
requires building KMS theory in Lean before the substrate-specific result can
even be stated. That is a foundational project on the scale of the substrate
work itself, not a finishing step.

**The cheap branch exists and is honest.** §5(A) offers an alternative: *"or
accept the base-3 presentation itself as a declared postulate of the theory."*
That costs no Lean. It does not derive the dictionary — it declares the input
the dictionary needs, which is what the book arguably already does by being
about a ternary substrate. Taking that branch converts (A) from "open gap" to
"declared postulate", which is a real improvement in honesty and zero
improvement in derivation.

---

## Gate (B) — confirm a number: THE JOINT TEST IS SATURATED

This is the finding. THE MAP reports the joint test as 1 hit / 1 miss and
says "as of now it reads coincidence", with the implication that filling more
rows is what comes next. **Filling more rows cannot change the verdict, and the
reason is structural.**

The dictionary is "σ(α_X) = the physical scaling exponent of sector X". A row
is testable only if sector X has an *a priori* measured physical scaling
exponent. Taking the nine sectors as they stand:

| sector | σ(α_X) | a priori physical scaling exponent? | evidential weight |
|---|---|---|---|
| QG | −0.0387 | yes — spectral tilt n_s−1 | **high** (precise non-round value) |
| NS | −1.308 | yes — Kolmogorov E(k) | **high** (precise non-round value) |
| Yang–Mills | 1 | yes — linear confining potential V(r) ∝ r¹ | **low** (round) |
| Poincaré | 0 | marginal / no scaling | **negligible** (round) |
| RH | 0 | marginal / no scaling | **negligible** (round) |
| P | −0.692 | **no** — complexity theory, no measured exponent | untestable |
| NP | +0.947 | **no** — same | untestable |
| Hodge | +0.496 | **no** — algebraic geometry | untestable |
| BSD | +0.571 | **no** — number theory | untestable |

Three consequences, and they close the gate:

1. **Only two sectors carry informative tests, and both are already filled.**
   QG (hit, 0.86σ) and NS (miss, 0.359). The informative surface of the map is
   exhausted.

2. **The round-σ rows cannot add evidence.** σ(α_YM) = 1 does match the linear
   confining potential exponent exactly, and that is a point in the
   framework's favour which should be stated rather than buried. But an
   exponent of 1 is the generic case in physics for dimensional reasons, so a
   match there is near-costless to achieve and carries little information. The
   same applies, more strongly, to the two σ = 0 sectors: "no power law" is
   what most quantities do. THE MAP calls these "the cheapest falsification
   target" — cheap to *test*, not informative when passed.

3. **A new row cannot be a prediction.** Extending the map to some tenth
   physical sector requires positing a tenth α-value, and α_X is ASSERTED per
   THE MAP. A row whose α is chosen after the observable is known is fitted,
   not predicted. This is the same structure already on the record as the
   forcing test — rank 10 in 10 unknowns, nothing forced — reached here from
   the observable side instead of the parameter side, and agreeing with it.

**Therefore gate (B) is not awaiting more work. It is complete, at
1 informative hit and 1 informative miss**, and under the project's own
standing rule ("compute honestly, at full strength either way; if the
computation does not support the claim, say so at full strength") the verdict
on the σ-dictionary is that it **is not supported**. One hit at 0.86σ against
one clear miss, with no further informative rows obtainable, reads as
coincidence — which is what THE MAP already said, now with the added fact that
no future measurement under this dictionary will move it.

---

## What this does and does not mean

**It does not touch the substrate.** `T_infinity_rigidity` and
`Substrate3Inf.trace_unique` are kernel-clean and public
(`398e3dfd`, tag `substrate-rigidity-v1`). The proven foundation, the proven
K-theoretic obstruction, and the one unconditional structural law
(τ(occupation) ∈ ℤ[1/3] at fixed level K) all stand exactly as recorded.

**What is priced out is one candidate map** — the σ-dictionary as the bridge
from substrate to observable. That bridge is now a closed question rather than
an open one, and closing it is a result: a falsifiable object was tested at its
full available power and did not survive. That is the outcome the map was
written to make possible.

**The constructive direction that remains is gate (A), and it is the
interesting one.** The reason σ had to carry the irrationals is the proven
obstruction: channel 1 (trace values) is confined to ℤ[1/3]. But σ is
presentation-level, not algebra-invariant — rigidity proves the algebra forgets
its digit labels. A dynamics on T_∞ would supply a **third** channel that is
algebra-intrinsic: for a one-parameter automorphism group with a non-tracial
KMS state, the GNS factor's Connes invariant is irrational-capable, and unlike
σ it is an invariant of the algebra-with-dynamics rather than of a chosen
labelling. That is a genuine route and it is not fitted. It is also months of
foundational Lean that does not exist in any library yet.

## One next action

Not more rows. The honest finish is to write gate (B)'s saturation into the
book as the result of the test — THE MAP already carries the scoreboard, and
this adds the one fact it is missing, that the scoreboard is final under this
dictionary. Then gate (A) is the research program, priced at "build KMS theory
first", to be started or declined deliberately rather than drifted into.

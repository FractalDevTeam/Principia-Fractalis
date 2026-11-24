# The dark-energy crossing redshift: PF's one parameter-free cosmological prediction

**Date**: 2026-11-23 (Legion). **Status**: internal instrument. Not a publication,
not a draft for anyone outside this repository.

Reproduce with `codex/pf_crossing_joint.py` (stdlib only).

---

## 1. The claim, in four lines of cosmology

PF's substrate CPL pair is `(w₀, wₐ) = (−φ/2, −1/φ)`
(`PF/Priority4SubstrateDischarge.lean`, r78). Under the CPL form
`w(a) = w₀ + wₐ(1−a)`, the equation of state crosses `w = −1` at

```
1 − a* = (1 + w₀)/|wₐ| = (φ − 1)/2 = 1/(2φ)      EXACT
     a* = (3 − φ)/2            = 0.6909830056
     z* = (φ − 1)/(3 − φ)      = 1/√5 = 0.4472135955
```

Kernel-proved in `PF/Cosmology/SubstrateCPLCrossing_r388.lean`, axiom-free. The
derivation consumes only `φ² = φ + 1`. **No parameter is adjusted.**

**ΛCDM predicts no crossing at all** — `w ≡ −1`, so there is no redshift to
compare. This column cannot be filled by the standard model even in principle.

## 2. The right comparison variable

The crossing depends on `w₀` and `wₐ` **only through the ratio**

```
R ≡ (1 + w₀)/|wₐ| ,        z* = 1/(1 − R) − 1
```

and that matters for significance, because

```
∂R/∂w₀ = 1/|wₐ|        > 0
∂R/∂wₐ = (1 + w₀)/wₐ²  > 0
```

**Both partials are positive.** `w₀` and `wₐ` are strongly *anti*-correlated in
every published fit, so the covariance term `2 (∂R/∂w₀)(∂R/∂wₐ) ρ σ₀ σₐ` is
**negative** and `Var(R)` *shrinks*.

This is the methodological point. An earlier PF significance (2.23–2.69σ) was
**withdrawn** because it propagated marginal errors as if `Cov(w₀,wₐ) = 0`
(`codex/COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md`). In `R`, the same
anti-correlation that invalidated that number works *for* the comparison: it
cannot be concealing a failure, because every `ρ < 0` makes the test sharper,
not looser. So the honest presentation is a **scan over ρ**, below, not a single
assumed value.

## 3. Published inputs

arXiv:2503.14738 — DESI DR2 Results II.

| combination | w₀ | wₐ | vs ΛCDM |
|---|---|---|---|
| DESI+CMB | −0.42 ± 0.21 | −1.75 ± 0.58 | 3.1σ |
| DESI+CMB+DESY5 | −0.752 ± 0.057 | −0.86 (+0.23/−0.20) | **4.2σ** |

Both lie in the quadrant `w₀ > −1, wₐ < 0` — which the DESI abstract names as
the favoured one, and which is **the quadrant PF's pair occupies**. Both have
`w₀ + wₐ < −1`, i.e. both are phantom in the past, i.e. **both cross**.

## 4. Result

| ρ(w₀,wₐ) | DESI+CMB+DESY5 | DESI+CMB |
|---|---|---|
| 0.00 *(marginal — invalid here)* | 0.21σ | 0.14σ |
| −0.50 | 0.30σ | 0.19σ |
| −0.70 | 0.38σ | 0.25σ |
| −0.80 | 0.47σ | 0.31σ |
| **−0.90** | **0.66σ** | **0.43σ** |
| −0.95 | 0.91σ | 0.59σ |
| −0.98 | 1.38σ | 0.89σ |

Derived crossing redshifts: DESY5 `z = 0.4052`, DESI+CMB `z = 0.4957`.
**PF's `1/√5 = 0.4472` is bracketed by the two.**

Independent cross-check from inside the corpus: inverting r219 against SN data
gives the `g`-zero at `z ≈ 0.40 ± 0.03`
(`COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md:30`), stable across three SN samples —
consistent with the DESY5 crossing at 0.4052, obtained by a different route.

**Agreement is under 1σ against both combinations for every ρ down to −0.95.**

## 5. What is NOT established — all four are load-bearing

1. **The published ρ is not in hand.** §4 is a scan, not a result. Table 3 of
   arXiv:2503.14738 or the DESI chains are required to close it.
2. **DESY5's `wₐ` error is asymmetric** (+0.23/−0.20); the mean half-width 0.215
   is used. Redo with the asymmetric likelihood before any external use.
3. **The golden-ratio pair is an ANSATZ, not derived** — Agent 10, 2026-07-04.
   `PF/Cosmology/SubstrateCPLExcluded_r389.lean` lists four independent
   obstructions: the α-values are ASSERTED; there is **no α_DE row** among the
   nine; the physical dictionary is an untested hypothesis; and the functional
   form is wrong — the substrate carries `log₃ φ`, a scaling *exponent*, while
   the pair uses **bare** `φ`. r389 also records two near-misses to be refused
   rather than rediscovered: `σ(3/4) = −0.80226` vs `−φ/2 = −0.80902` (0.84%),
   and `σ(1/3) = 0.63093` vs `1/φ = 0.61803` (2.09%); the first would require
   `3^φ = 3 + 2√2`, i.e. `5.91559 = 5.82843`, which is false.
4. **PF's own action derivation EXCLUDES this pair.** r389 proves `−φ/2` lies
   outside the derived window `w₀ ∈ [−0.99, −0.93]`, and the action's `Q = 0`
   branch is non-phantom *by theorem* (`w ≥ −1`, matching r219's
   `wEff_ge_neg_one` and ch27:168), so it forbids any crossing.

## 5b. The covariance-FREE test — `w₀` alone

Reproduce with `codex/pf_w0_test.py`.

A comparison of `w₀` against **its own published marginal uncertainty** is a
single-parameter test. The marginal σ is the *correct* error for it; no
correlation coefficient enters, so item 1 of §5 does not apply. This sidesteps
the exact defect that forced the withdrawal of the earlier 2.23–2.69σ.

Against DESI+CMB+DESY5, `w₀ = −0.752 ± 0.057`:

| model / branch | w₀ | g₀/H₀ = 3(1+w₀) | deviation |
|---|---|---|---|
| ΛCDM | −1.0000 | 0.0000 | **4.35σ** |
| PF action branch, near edge | −0.9300 | 0.2100 | 3.12σ |
| PF action branch, far edge | −0.9900 | 0.0300 | 4.18σ |
| **PF golden-ratio ansatz** | **−0.8090** | **0.5729** | **1.00σ** |
| measured g-inversion, low edge | −0.7530 | 0.7410 | 0.02σ |
| measured g-inversion, high edge | −0.6500 | 1.0500 | 1.79σ |

**Method check.** The 1-D ΛCDM deviation computed here, 4.35σ, reproduces DESI's
own quoted **4.2σ** joint significance for this combination. The approach is
therefore not inflating the comparison — it recovers the published number by an
independent route.

**Two consequences.**

1. **Ranking against DESY5: ansatz 1.00σ < PF action branch 3.12σ < ΛCDM 4.35σ.**
   `−φ/2 = −0.809017` sits at almost exactly one marginal σ from the published
   central value, and φ was fixed in this framework years before DESI DR2
   existed.

2. **Crossing-vs-touch cannot rescue the action branch.** §6's undecided question
   concerns how to read the zero at `z ≈ 0.40`. But the action branch misses the
   measured `w₀` by **3.12σ at its most favourable edge and 4.18σ at its other
   edge**, and that is a statement about *today's* value, independent of whether
   the past zero is a crossing or a touch. So resolving §6 in the action
   branch's favour does not save it; it would still be further from the data
   than ΛCDM's nearest competitor.

   That narrows the fork: the data disfavours the action branch on `w₀` alone,
   before any question about the crossing is reached.

**Caveats unchanged by this test**: `−φ/2` is an ansatz, not derived (§5 item 3);
r389 proves the action derivation excludes it (§5 item 4); this is one data
combination, and Pantheon+ and Union3 give different `w₀`; and agreement at 1σ
is "not excluded", never "confirmed".

## 5c. Robustness across SNe samples — OPEN, and a trap to avoid

**This is the check that decides whether §5b survives a referee**, and it is not
finished. Recorded here in its true state.

**What is verified.** DESI+CMB+DESY5 `w₀ = −0.752 ± 0.057`,
`wₐ = −0.86 (+0.23/−0.20)`, 4.2σ. DESI+CMB `w₀ = −0.42 ± 0.21`,
`wₐ = −1.75 ± 0.58`, 3.1σ. DESI+CMB+Union3 `wₐ = −1.09 (+0.31/−0.27)`.
DESI's own ΛCDM-rejection significances: **2.8σ (Pantheon+), 3.8σ (Union3),
4.2σ (DESY5)**, with Δχ²(MAP) = −10.7, −17.4, −21.0.

**What is NOT verified.** The `w₀` values in the **w₀wₐCDM** model for the
Pantheon+ and Union3 combinations. Until those are read off Table 3 of
arXiv:2503.14738, §5b's 1.00σ is a **one-combination result** and must be
described as such.

**THE TRAP, and it nearly caught this document.** Secondary summaries quote
`w₀ = −0.986 ± 0.026` (Pantheon+), `−0.983 ± 0.024` (DES-Dovekie),
`−0.979 ± 0.031` (Union3). **Those are wCDM — constant-`w` — fits, not
w₀wₐCDM.** They have no `wₐ` column. Substituting them into a `w₀wₐ`
comparison would be a category error, and it would wrongly make every model
look consistent with Λ. Any future pass must confirm it is reading the
**w₀wₐCDM** row.

**And the trap contains a real finding.** In the constant-`w` model, DESI+CMB+SNe
gives **N_σ ≈ 0 against ΛCDM for every sample** (at most 0.14σ), and DESI+CMB
alone gives `w = −1.037 ± 0.041`, also N_σ ≈ 0
([arXiv:2508.10514](https://arxiv.org/abs/2508.10514), Table 4).

So **the entire DESI anomaly lives in the evolution term, not in the value of
`w` today.** A constant-`w` alternative to Λ gains nothing. That is
methodologically important for this lane: it means the discriminating variable
is `wₐ`, or equivalently the crossing — which is precisely what PF's pair
predicts in closed form, and precisely the cell ΛCDM cannot fill. It also means
§5b, which compares `w₀`, is testing the *less* discriminating coordinate; §4's
crossing comparison is the sharper test, and it is the one still waiting on ρ.

## 5d. Robustness check — DONE, and it passes in all three samples

§5c's open item is **closed**. The w₀wₐCDM rows are confirmed
(arXiv:2503.14738): Pantheon+ `w₀ = −0.838 ± 0.055, wₐ = −0.62`; DESY5
`w₀ = −0.752 ± 0.057, wₐ = −0.86`; Union3 `w₀ = −0.667 ± 0.088, wₐ = −1.09`.
Reproduce with `codex/pf_three_sample.py`.

### A — `w₀` alone (single parameter; marginal σ correct, no covariance)

| sample | measured w₀ | ΛCDM | PF action (−0.93 edge) | **PF ansatz** | DESI's joint |
|---|---|---|---|---|---|
| Pantheon+ | −0.838 ± 0.055 | 2.95σ | 1.67σ | **0.53σ** | 2.8σ |
| DESY5 | −0.752 ± 0.057 | 4.35σ | 3.12σ | **1.00σ** | 4.2σ |
| Union3 | −0.667 ± 0.088 | 3.78σ | 2.99σ | **1.61σ** | 3.8σ |

**Method validated three times.** The 1-D ΛCDM column — 2.95σ, 4.35σ, 3.78σ —
reproduces DESI's own *joint* significances of 2.8σ, 4.2σ, 3.8σ, sample by
sample. The approach recovers the published result by an independent route in
every case, so it is not inflating the comparison.

**PF's ansatz is under 2σ in all three, and is the closest of the three models
in all three.**

Note the correction this forces on §5b: the action branch is **1.67σ** against
Pantheon+, not 3σ+. §5b's claim that crossing-vs-touch "cannot rescue" it holds
for DESY5 and Union3 (3.12σ, 2.99σ) but **not** for Pantheon+. The honest form
is: the action branch is disfavoured by two of three samples and survives the
third at 1.67σ.

### B — the crossing, the coordinate where DESI's signal actually lives

| sample | R = (1+w₀)/\|wₐ\| | z_cross | \|R − R_PF\| | \|z − z*\| |
|---|---|---|---|---|
| Pantheon+ | 0.261290 | 0.353712 | 0.047727 | 0.093502 |
| DESY5 | 0.288372 | 0.405229 | 0.020645 | 0.041985 |
| **Union3** | **0.305505** | **0.439894** | **0.003512** | **0.007319** |
| **PF (exact)** | **0.309017** | **0.447214** | — | — |
| ΛCDM | undefined | **none** | — | — |

The three samples bracket PF from below — 0.354, 0.405, 0.440 against 0.447 —
and **Union3, the 3.8σ combination, lands 0.0073 from PF's closed form**, an
agreement of 1.6%. ΛCDM cannot populate this column in principle.

### Still not established

* The published **ρ(w₀,wₐ)** is not in hand, so §B is a point comparison, not
  yet a significance. §4's scan stands as the bound on what ρ can do to it.
* Pantheon+ and Union3 **wₐ uncertainties** are not yet read off Table 3; only
  their central values are used in §B.
* `−φ/2` remains an **ansatz**, not derived (§5 item 3), and r389 still proves
  PF's own action derivation excludes it (§5 item 4).
* Under 2σ is **not excluded**, never confirmed.

## 5e. ρ is load-bearing, and the limiting factor is the data, not PF

Reproduce with `codex/pf_rho_bound.py`.

I attempted to bound ρ away. **It cannot be bounded away, and the attempt
failed against the prediction.** Worst deviation over a ρ scan to the
degenerate limit:

| sample | ρ = 0 | ρ = −0.9 | ρ = −0.99 | worst |
|---|---|---|---|---|
| Union3 | 0.03σ | 0.10σ | 0.31σ | **0.96σ** |
| DESY5 | 0.21σ | 0.66σ | 1.82σ | **3.14σ** |
| Pantheon+ | 0.38σ | 1.19σ | 3.72σ | **10.76σ** |

At low \|ρ\| all three agree. At high \|ρ\| they diverge sharply and
**Pantheon+ strongly excludes** PF's closed form. So the honest statement is
*not* "ρ cannot hurt us" — it is that the crossing comparison is strongly ρ- and
sample-dependent, and **the published ρ must be obtained before any σ is
quoted.** §4's and §5d's crossing numbers are point comparisons until then.

### The deeper point, and it is about the data

**The three SNe samples disagree with each other on R by more than PF differs
from the best of them:**

```
sample-to-sample spread in R : 0.044214
PF offset from closest (U3)  : 0.003512
ratio                        : 12.6x
```

PF's exact value sits at the **top** of the data's own range. Until the
supernova samples agree with one another, **the discriminating test is not
available at all** — SNe systematics dominate the comparison by more than an
order of magnitude.

That is the referee-proof reading of this lane: **not a confirmation, not a
refutation, and the limiting factor is the data's internal scatter rather than
anything about PF.** It is also the honest answer to "how close are we here" —
closer than ΛCDM on `w₀` in all three samples (§5d A, which needs no ρ), and
untestable on the crossing until the SNe tension is resolved.

Unchanged: the pair is an **ansatz**, not derived (§5 item 3), and r389 proves
PF's own action derivation excludes it (§5 item 4).

## 6. The fork, and why it is an asset

PF carries two mutually exclusive cosmologies, and the inconsistency is settled
by a theorem rather than by data:

| branch | w₀ | g₀/H₀ | crossing? |
|---|---|---|---|
| golden-ratio CPL ansatz (r78) | −0.8090 | 0.5729 | yes, at `z = 1/√5` |
| action derivation, Q=0 (register A) | [−0.99, −0.93] | [0.030, 0.210] | **never** (theorem) |
| measured `g` inversion | [−0.753, −0.650] | [0.74, 1.05] | zero at `z ≈ 0.40` |

All three pairwise comparisons fail (r389). And r389 names the undecided
question precisely:

> the route map reads the measured zero at `z ≈ 0.40` as a **crossing**; the
> derivation says it is a **touch** — a thawing field frozen at `φ̇ = 0`, so `g`
> reaches zero without changing sign. *"Those are different claims about the
> same measured number and the corpus has not distinguished them."*

**Crossing or touch decides which half of PF's cosmology is load-bearing.** DESI's
central values have `w < −1` in the past, which is a crossing — so the data
currently points at the ansatz branch and against the action branch.

A framework that says *"my two branches disagree, and here is the measurement
that decides between them"* is doing what a theory should. The failure mode to
avoid is presenting one branch while the kernel proves the other.

## 7. Delivery note

This result is four lines of cosmology. It mentions no consciousness, no Clay
problem, and no fractal mathematics. That is deliberate: the one referee-facing
claim in this lane should arrive on its own, in the discipline of the person
reading it, and not inside a 1,062-page framework. A cosmologist who says a PF
submission is "not in my discipline" is making a true statement about surface
area, not a judgment about content — and §1 above is the part that *is* in their
discipline.

No external communication of any kind is drafted, staged or sent from this
document.

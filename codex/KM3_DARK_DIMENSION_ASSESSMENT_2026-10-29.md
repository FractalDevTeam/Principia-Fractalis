# KM3-230213A / dark dimension: what is borrowable, measured against the corpus

**Date:** 2026-10-29 (Legion). Assessment of a supplied research report
(`KM3-230213A and the Dark Dimension — Research Report`, researched 29–30 Oct
2026) against the PF corpus. Labels **FACT** (measured in the corpus or stated
in the report) / **JUDGEMENT** / **OPEN**.

---

## The report is sound; its one open question is now answered

The report grades ten explanations for KM3-230213A, gives none of them
"Supported", and concludes for PF: *thematic fit only, no shared numbers, treat
the dark dimension as a competitor to track, not support to cite.* **That
verdict stands and this note does not weaken it.** In particular: do **not**
cite KM3-230213A as evidence for anything in PF. It is one event, 90% energy
range 72 PeV–2.6 EeV (a factor ~36), no counterpart, and the fifth-dimension
reading is called "very speculative" by its own lead author.

The report closes with one explicit gap:

> The program's specific w(z) values were not supplied for this research, so
> §E.1 is a structural comparison, not a numerical one. If those values are
> provided, the phantom-crossing point is the first thing to re-check.

They are in the corpus. Supplying them changes two of the report's conclusions.

## FACT — what the corpus actually contains

| | value | where |
|---|---|---|
| substrate CPL pair | `(w₀, wₐ) = (−φ/2, −1/φ) ≈ (−0.8090, −0.6180)` | `Priority4SubstrateDischarge.lean:87,94` (r78) |
| exact w-bridge | `w(t) = −1 + g/(3H)`, and `−1 ≤ w ⟺ 0 ≤ g` | `EquationOfStateBridge_r219.lean` |
| non-phantom bound | `w ≥ −1` on `(0,1]` ⟹ `wₐ ≥ −1 − w₀` | `cpl_nonphantom_forces_wa_bound` |
| **measured g** | `g₀ ≈ 0.74–1.05 H₀`, **zero at z ≈ 0.40 ± 0.03**, stable across 3 SN samples | `COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md:30` |
| route-level status | "PF does **NOT** pin w₀, wₐ quantitatively" | `MODIFIED_GRAVITY_VS_DESI_2026-10-11.md:57` |

A `g` sign change is, by r219's IVT lemma, a **located crossing** of `w = −1`.
So the corpus's own measurement puts PF on the **crossing** branch at
**z ≈ 0.40**.

## Finding A — the report's "no numbers touch" is wrong, in one place

The report checks explicitly and concludes *"Do any numbers quantitatively
touch? Checked explicitly — no."* With PF's numbers in hand, one does:

* PF: `w = −1` crossing **measured at z = 0.40 ± 0.03**.
* Dark dimension: a **Casimir-quintessence realisation crosses at z ~ 0.4**
  (report §E.1; traced there to `arXiv:2603.19819`).

**JUDGEMENT — and this is the part that matters.** This is **not** independent
corroboration, and must not be presented as such. PF's `g` was *measured by
inverting r219 against SN data*; the Casimir-quintessence model is *also fit to
DESI/SN data*. Two fits to substantially the same data agreeing on a crossing
redshift is close to expected, not evidential. It would only be corroboration if
one side **derived** z ≈ 0.4 instead of fitting it, and PF does not — the route
map labels `g` MEASURED, not derived.

What the agreement **is** worth, and it is not nothing: it is **defensive**. A
mainstream string-cosmology construction (Vafa-lineage) puts the crossing in the
same place PF's inversion does. So PF's crossing is not an exotic artifact of its
own machinery, and "your model needs phantom crossing, which is unphysical" is
answerable by citation rather than argument. Framing value, per the report's own
§F.2 — not evidence.

## Finding B — an internal inconsistency, now kernel-verified (r387)

Substituting r78 into r219's bound:

    wₐ      = −1/φ      ≈ −0.6180
    −1 − w₀ = −1 + φ/2  ≈ −0.1910

and `−0.6180 ≥ −0.1910` is **false** by 0.427. So r78's pair is phantom in the
past (`w₀ + wₐ ≈ −1.4271`) and **cannot satisfy the hypothesis of r219's own
theorem**. Proved in `PF/Cosmology/SubstrateCPLPhantomCheck_r387.lean`
(`e569cdcd`), three ways, the last by contraposition *through* r219 so the
inconsistency is exhibited by the corpus's own theorem.

Three-way, in fact: r78 pins the pair, the route-map note says PF does *not* pin
it, and r219's bound excludes the pinned value on the monotone branch. **No
codex note mentions `substrate_w_a` or the golden-ratio pair at all** — greped
all of `codex/*.md`. It has sat unreconciled.

**Nothing is withdrawn.** Both r78 and r219 stand; what is established is joint
inconsistency with `g ≥ 0`. And since the measured `g` has a zero at z ≈ 0.40,
the branch the data picks is the crossing one — so what needs revisiting is
**`hg0 : 0 ≤ g` as a global assumption**, not r78's numbers. `g = φ̇/M` is
measured here, not derived, and `g ≥ 0` is an assumption, so nothing proved
privileges the monotone branch.

## Finding C — the real competitive threat, and it is not the neutrino

Bedroya–Obied–Vafa–Wu (`arXiv:2507.03090`) fit DESI DR2 + SNe with an evolving
dark sector — `V = V₀e^{−cφ}`, dark-matter mass `m_DM = m₀e^{−c′φ}`,
`c′ ≈ 0.05 ± 0.01` — **at the same statistical significance as CPL `w₀wₐ`**, and
in it DESI's apparent `w < −1` is an **artifact of assuming constant dark-matter
mass**, with no true phantom crossing.

**JUDGEMENT.** That is a direct competitor for the *same signal PF's crossing
explains*, and it is the sharpest thing in the report for PF's purposes. If the
apparent phantom behaviour is a constant-`m_DM` fitting artifact, then PF's
`z ≈ 0.40` crossing — obtained by inverting r219 against fits that assume
constant `m_DM` — is explaining an artifact. **This is a live risk to the DE
lane, independent of anything about KM3NeT.**

It also cuts the other way as an opportunity: PF has a **sharp number**
(`z = 0.40 ± 0.03`, stable across three SN samples) where the dark-dimension
side has a *family* (`c`, `c′`, exponential potentials). Per the report's §F.4,
Euclid/DESI `w(z)` reconstructions are expected to separate exponential-radion,
phantom-crossing, and specific-`w(z)` families. A sharp located crossing is the
more falsifiable claim, and that is PF's advantage to press.

## What to do, in order

1. **Resolve Finding B.** Decide the status of `hg0 : 0 ≤ g` as a global
   assumption versus a local one. Pablo's call — it is a modelling decision, not
   a derivation.
2. **Price Finding C.** Re-derive `g` under an evolving-`m_DM` background and see
   whether the z ≈ 0.40 zero survives. If it does not, the DE lane's one
   measured number is parameterisation-dependent and must be relabelled.
3. **Do not cite KM3-230213A.** Per the report, and I concur.
4. Optional, cheap: cite `arXiv:2603.19819` defensively wherever the manuscript
   defends phantom crossing, with the "two fits to one dataset" caveat stated.

## What is NOT claimed

Not claimed: that the dark dimension supports PF; that the z ≈ 0.4 agreement is
evidence for either framework; that KM3-230213A bears on PF at all. Not claimed:
anything about the report's own primary sources beyond what it states — the
Casimir-quintessence z ~ 0.4 figure is taken from the report and **was not
independently checked against `arXiv:2603.19819`**. Not claimed: any revision to
r78 or r219.

**OPEN:** whether PF's z ≈ 0.40 survives an evolving-`m_DM` background. That is
Finding C, and it is the question this document is actually useful for.

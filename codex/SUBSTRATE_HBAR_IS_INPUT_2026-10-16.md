# Does the substrate derive `hbar`? — verdict: NO, it is an input everywhere

**Date:** 2026-10-16 (Legion). Report only; the corpus's own words, with quotes.
Question: the mass-scaling obstruction killed `D = hbar/2m` from `G, c, m`.
Does the **substrate / timeless field** route survive?

**Verdict: there is no substrate derivation of `hbar` in this corpus. `hbar` is
imported as a primitive, including into the timeless field's own evolution
equation. Conclusion (iv) of the gap-2 decomposition is genuinely an input.**

---

## 1. `ch34A_substrate_theorem.tex` — the substrate theorem says nothing

`grep -c hbar ch34A_substrate_theorem.tex` = **0**.

The chapter that would own a substrate derivation of `hbar` does not mention
`hbar` at all. (Its "Nelson" occurrences are **Hadwiger-Nelson**, the
graph-colouring problem — unrelated to stochastic mechanics.)

## 2. `ch04_timeless_field.tex` — `hbar` is inside the postulated dynamics

Three occurrences, all within the *assumed* evolution law:

> `\frac{d}{dt}a(t) = \frac{i}{\hbar}[H, a(t)] + \mathcal{L}[a(t)]`
> (eq:field-evolution, :658)

> `a(t) = e^{iHt/\hbar} a(0) e^{-iHt/\hbar}` (:673)

> **Proposition (Reduction to Schrödinger)** "For states localized at level
> `k`, equation (eq:field-evolution) reduces to the Schrödinger equation:"
> `i\hbar \frac{\partial}{\partial t}|\psi_k(t)\rangle = H_k |\psi_k(t)\rangle`
> "on `\mathcal{H}_k = \mathbb{C}^{3^k}`." (prop:schrodinger, :683)

The timeless field's dynamics is **written with `hbar` already in it**. The
"Reduction to Schrödinger" therefore recovers `hbar` because `hbar` was put
into the premise. **Verdict: input.**

## 3. `ch07_constants.tex` — four uses, all with `hbar` given; one reversed

* :148 "the minimum transferable action is quantized in units of
  `\hbar \cdot (\pi/10)`" — a postulate **about** `hbar`. **Input.**
* :590 `\alpha_{EM} = e^2/(4\pi\epsilon_0\hbar c)` — the standard
  definition. **Input.**
* :627 `G = \frac{\hbar c}{m_P^2}` — note the direction: this derives **`G`
  from `hbar`**, the reverse of what a substrate route needs. **Input.**
* :635 `\tau_{\mathcal{C}} = \hbar/c^2` — **input**, and defective (below).

### The one place `hbar` is asked to do structural work, and it fails

**Proposition (Gravity from Consciousness Time)**, :632-635:

> `G = \frac{c^3}{m_P^2} \cdot \tau_{\mathcal{C}}`
> "where `\tau_{\mathcal{C}} = \hbar/c^2` is the time scale for consciousness
> to interact with spacetime curvature."

accompanied (:intuitive block) by

> "The consciousness time constant `\tau_{\mathcal{C}} \sim 10^{-43}` seconds
> (the Planck time)"

Three defects, all checked by arithmetic on CODATA values (computed, not
recalled):

1. **It is the same equation as :627.** Substituting,
   `(c^3/m_P^2)(\hbar/c^2) = \hbar c/m_P^2`. The proposition restates the
   preceding line with `\hbar/c^2` relabelled a "consciousness time constant".
2. **Dimensional error.** `\hbar/c^2` has units
   `(J s)/(m^2 s^{-2}) = kg\,s` — **mass x time, not a time.** It cannot be a
   "time scale". Numerically `\hbar/c^2 = 1.1733694e-51` (kg s), whereas the
   actual Planck time is `\sqrt{\hbar G/c^5} = 5.3912464e-44` s. The asserted
   identification with `~10^{-43}` s is wrong by ~8 orders of magnitude even
   setting the units aside.
3. **`m_P` is never defined in the chapter** — it occurs only in these two
   equations. If it is the standard Planck mass then `m_P = \sqrt{\hbar c/G}`
   by definition and `G = \hbar c/m_P^2` is **that definition rearranged**: a
   tautology (checked: both sides `6.6743e-11` by construction). It derives
   nothing about `G` or `hbar`.

## 4. Repo-wide

No chapter anywhere claims to derive `hbar` (searched for "derive hbar",
"hbar derived", "origin of hbar", "hbar emerges", "emergent hbar" across all
chapters: no derivation claim). `hbar` appears in 12 chapters, always as a
given constant.

---

## Verdict on gap-2 conclusion (iv)

**`D = hbar/2m` is an input, not a substrate consequence.**

Two independent obstructions now stand:

* **classical route** — the only `L^2 T^{-1}` combination of `G, c, m` is
  `Gm/c`, which scales as `m^{+1}` while `hbar/2m` scales as `m^{-1}`; the
  mass dependence is inverted and the magnitudes differ by `~10^{44}`
  (`codex/GAP2_FLUCTUATION_LAW_SCOPE_2026-10-16.md`).
* **substrate route** — the corpus imports `hbar` into the substrate's own
  evolution equation, so any `hbar` recovered downstream was put in upstream.
  That is **relocation, not derivation**.

**Consequence for the gap-2 attack:** if a path-space variational principle is
built on the substrate dynamics of `ch04`, it will reproduce `D = hbar/2m` —
but only because `hbar` entered through `eq:field-evolution`. That must be
stated as an input in any write-up, not presented as a derivation.

**Honest boundary.** This establishes that *this corpus* contains no
derivation of `hbar`. It is not a proof that no substrate derivation could
exist. What it does rule out is the specific claim that the existing
timeless-field formalism supplies one.

**Repair targets found incidentally** (ch07, Prop "Gravity from Consciousness
Time"): the `kg\,s`-vs-`s` dimensional error, the `10^{-43}` s
misidentification, and the tautological `G = \hbar c/m_P^2`. These are
independent of the `hbar` question and are worth a manuscript correction.

# Cosmology, 2026-08-10 — the w(a) bridge, and what it does to ch26

The cosmology pillar had **two** Lean files against 138 for the α-skeleton. It is
also where the framework's central thesis lives and the only pillar with a
falsifiable number available against 2025 data. This record levels it.

Every number below was computed here and checked. Companion Lean stone: **r219**
(`PF/EquationOfStateBridge_r219.lean`).

---

## 1. THE BRIDGE — from a kernel-checked ODE to an observable

`PF/ModifiedFriedmann_r187.lean` proves, kernel-clean:

    LambdaEff Λ₀ g t = Λ₀ · exp(−∫₀ᵗ g)
    hasDerivAt_lambdaEff :  Λ_eff′ = −g · Λ_eff

Since `ρ_Λ ∝ Λ_eff`, and the single-component continuity equation is
`ρ′ + 3H(1+w)ρ = 0`, i.e. `w = −1 − ρ′/(3Hρ)`, substituting `ρ′/ρ = −g` gives

    ┌──────────────────────────────────┐
    │   w(t) = −1 + g(t) / (3 H(t))    │   exact, no approximation
    └──────────────────────────────────┘

**Immediate consequence.** `g ≥ 0 ⟺ w ≥ −1`. And `g ≥ 0` is exactly r187's
hypothesis `hg0` for `lambdaEff_antitone`. So **the monotone-decay form of the
framework is non-phantom and cannot cross w = −1.** Crossing requires `g` to
change sign — which the ODE permits (it needs only continuity) and which the
monotonicity theorem forbids.

---

## 2. g IS NOW A MEASURED QUANTITY

Running the bridge backwards on DESI DR2 (2025):

| dataset | w₀ | wₐ | g₀/H₀ | wₐ needed for g≥0 | tension | crossing z |
|---|---|---|---|---|---|---|
| DESI+CMB | −0.667 ± 0.088 | −1.09 ± 0.29 | 0.999 | ≥ −0.333 | 2.6σ | 0.440 |
| DESI+CMB+DESY5 | −0.752 ± 0.057 | −0.86 ± 0.22 | 0.744 | ≥ −0.248 | 2.8σ | 0.405 |
| DESI+CMB+Union3 | −0.65 ± 0.10 | −1.27 ± 0.40 | 1.050 | ≥ −0.350 | 2.3σ | 0.380 |

Two numbers the framework did not have before:

* **g₀ ≈ 0.74 – 1.05 H₀** — the suppression rate today, in Hubble units, read off
  the data through the framework's own ODE. O(1) in H₀, which is at least the
  right order.
* **a zero of g at z ≈ 0.40 ± 0.03** — remarkably stable across three
  independent supernova samples.

The monotone form is disfavoured at **2.3–2.8σ**. Not dead. Under pressure.

---

## 3. DOES THE CORPUS DEFINE g? No — and taking ch26 seriously kills it.

**There is no independent definition of `g` anywhere in the corpus.** ch26's
suppression is exponential in a *volume*, not a time:

    S_cons = exp[−0.95 · V_cons / V_char]        (ch26:221)

and ch26 itself records, at `:261`, that the 10⁻¹²⁰ match is
*"**engineered, not derived** … the observed target sets the construction, this
is a fit to a known value, not an independent first-principles prediction."*
The first pass of that calculation reaches `Λ_eff ≈ Λ₀ exp(−10⁻⁵⁵)` — "barely any
suppression" in the chapter's own words — and `V_eff = (ct)³` is then introduced
to move the exponent to 10¹²⁸.

**But `V_eff = (ct)³` is time-dependent, so it does imply a g(t).** Take it at
face value:

    β(t) = K t³   ⟹   g(t) = −d ln Λ_eff/dt = 3 K t²

That is a **derived** g(t), not a posit. Fix `K` by the chapter's own target:

    K t₀³ = 120 ln 10 = 276.310
    g(t₀) = 3 K t₀² = 828.93 / t₀
    with H₀t₀ = 0.964 (ΛCDM, Ωm = 0.315):
    g₀/H₀ = 859.9

Against the measured value:

| | g₀/H₀ | implied w₀ |
|---|---|---|
| ch26 mechanism over cosmic time | **859.9** | **+285.6** |
| DESI DR2 (via the bridge) | 0.744 ± 0.17 | −0.752 ± 0.057 |

**1156× too large.** The implied w₀ = +285.6 against an observed −0.752 is not a
marginal failure; it is excluded by ~5×10³ σ.

### The fork, and both branches close

1. **Suppression over cosmic time** at rate `g ∝ t²` ⟹ `w₀ = +285.6`. Absurd.
   Excluded outright.
2. **Therefore the suppression must be primordial and static since** ⟹ `g ≈ 0`
   today ⟹ `w = −1` exactly ⟹ degenerate with Λ, and inconsistent with DESI's
   `w₀ = −0.752` at **4.4σ**.

**Either branch fails. The ch26 mechanism cannot produce the observed equation
of state.** This is a quantitative refutation, not a scope note, and it is
independent of the "engineered" admission already at `:261` — that admission is
about the *fit*; this is about the *rate*.

---

## 4. WHAT SURVIVES, AND IT IS NOT NOTHING

* **r187's ODE is real.** Kernel-clean, unchanged, and now load-bearing rather
  than decorative: it is what makes the bridge possible.
* **r219's bridge is real.** `w = −1 + g/(3H)` is a theorem about the framework's
  own postulated law.
* **`g` moved from undefined to measured.** Before today it was a free function
  with no definition and no constraint. It is now pinned by data at two points:
  `g₀ = 0.744 ± 0.17 H₀` and `g(z ≈ 0.40) = 0`. Any future first-principles
  derivation of `g` has two numbers it must hit — and if it produces a monotone
  `g ≥ 0`, it is already in 2.8σ tension.

That is the levelling move the cosmology pillar needed: from two files and zero
testable numbers to three files and two measured constraints.

---

## 5. SEPARATE FINDING — the ΛCDM comparison paper's density profile

`pablo_context/scientific_work/latex_documents/Demonstration of the Superiority
of Fractal Resonance Ontology over Standard.tex` (title: *Mathematical
Demonstration of the Superiority of Fractal Resonance Ontology over Standard
ΛCDM Cosmology*). **Not in the versioned repo** — see §6.

Its central formula is

    ρ_Cohen(r) = ρ₀ · r_c²/(r² + r_c²) · R_f(3π/2, ln(r/r_c))

Three findings, all checked against r212:

1. **It is complex-valued.** `w = e^{iπ·3π/2} = −0.6188 + 0.7855i`, so
   `R_f(3π/2, ·) ∈ ℂ` and the profile returns a complex density. The `r_c`
   formula uses modulus bars; the profile formula does not. Type error in the
   load-bearing equation.
2. **The evaluation point is in the divergent region.** `σ(3π/2) = −1.30801`
   (r212), so the series needs `r > e^σ r_c = 0.2704 r_c`. With
   `r_c = |R_f(3π/2,1)| r_s = 0.92430 r_s`, the paper's `r = 0.01` kpc gives
   `s = ln(r/r_c)` between −4.5 and −6.1. The analytic continuation is finite
   there (no real pole: poles sit at `s = σ + i(arg χ + 2πk)/ln 3` with
   `arg χ = −0.90356`, and no integer `k` makes that zero) — but the paper writes
   a series and evaluates it where the series does not exist.
3. **One thing comes out clean:** `|R_f(3π/2, 1)| = 0.9243`, so
   `r_c = 0.9243 r_s`. A genuine derived relation.

**The structural problem is larger than any of the three.** The factor
`ρ₀ r_c²/(r²+r_c²)` is a pseudo-isothermal core; on its own it gives
`ρ(0) = ρ₀`, finite. **It already solves the cusp problem before R_f enters.**
So the claimed resolution comes from cored phenomenology — standard, correct,
and what dwarf rotation curves have wanted since the 1990s — and not from the
fractal resonance function. The distinctive ingredient is not load-bearing for
the result claimed.

Same pattern as ch23: real target, sound intuition, novel machinery not doing
the work. What *is* right: the cusp–core problem is a genuine ΛCDM difficulty,
NGC 1052-DF2 is a real and famously DM-deficient system, and
`∇^μ(T+C) = J^C_ν ≠ 0` is a well-posed modification rather than a slogan.

---

## 6. DATA-PRESERVATION EXPOSURE — the largest one in the setup

**None of the 28 Academia.edu papers is under version control.** They live in
`pablo_context/scientific_work/latex_documents/`, `XOUT/PF_MANUSCRIPTS/`,
`With Love for C and M/PDF's/`, and various `ARCHIVE/` trees — never in
`~/Principia-Fractalis`. Includes *The Ocean of Timeless Existence*, the ΛCDM
comparison, *Consciousness-Extended General Relativity*, the Weinstein Geometric
Unity paper, and the Millennium-problem papers.

Bigger than the 171 orphaned Lean files, because the Lean files at least compile
standalone and are reproducible. These are not reproducible if a disk fails.

---

## 7. QUEUE

1. **r219** — the bridge as a Lean stone. In flight.
2. **Does anything derive g?** ch26 does not. If nothing does, the framework's
   cosmology axis is a measurement, not a prediction — and that should be stated
   in ch26/ch27's ledgers.
3. **Version the 28 papers.**
4. The 171 orphaned Lean files.
5. ch26 ledger: the rate refutation in §3 above.

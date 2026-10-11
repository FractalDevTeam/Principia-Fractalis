# Can the substrate fix M, f, ch₂(a)? — the dark-energy parameters, 2026-10-11

Author: Pablo Cohen. Task: derive the three undetermined parameters of PF's
Λ_eff dark-energy mechanism (ch08) — M, f, ch₂(a) — from the substrate.
Verified under my own hand; four-label ledger (PROVEN / STRUCTURAL / EXTERNAL / OPEN).
(rev 2: the first draft's "proven impossibility" framing was an overclaim and is
corrected here per review — see "Answer, first".)

## Answer, first

Two claims must be kept apart, and the first draft wrongly merged them:

- **Concrete finding (defensible):** the present PF construction does **not**
  independently determine M, f, or the source profile ch₂(a). Verified: no Lean
  file and no chapter derives f or ch₂(a) (targeted grep empty); M has only a
  necessary lower bound, not a value.
- **Impossibility (NOT established, retracted):** "the substrate *cannot* derive
  them" would require an impossibility theorem with explicit assumptions.
  K₀(T_∞)=ℤ[1/3] does not supply one — that result proves the α-*ratios* (π) lie
  outside the trace's range; it does not prove K-theory captures every observable,
  nor that no added dynamics could fix these parameters. The "proven obstruction"
  framing is withdrawn.

What IS a sound obstruction is narrower and purely **dimensional**: T_∞ is a
*dimensionless* C*-algebra, so without a scale-setting input it cannot select an
**absolute** energy (M, f in GeV). But that forbids only absolute scales — it does
**not** forbid a dimensionless ratio (M/M_Pl) or a function of the dimensionless
scale factor a. Either of those the substrate *could* in principle fix — **if it
supplied dynamics** (evolution equations + initial/boundary conditions). As given,
it does not. So the missing ingredient is **dynamics, not dimensionality**, and the
honest status is "undetermined in the current construction", not "impossible".

Consequence (unchanged): a quantitative DESI test needs a chosen ch₂(a). A chosen
profile can still be tested — but **fitting begins the moment the profile is
selected or adjusted using the observations being tested**. So the DESI status
stays retrospective qualitative compatibility, not confirmation.

## The three parameters, structure vs value

### M — field-excursion scale in V(φ) = (Λ₀/κ)e^{−φ/M}

- **STRUCTURAL (Lean):** M is the *sole* scale in the exponential — suppression
  depends only on (ψ−φ)/M, no hidden second scale
  (`suppression_factor_is_scaled_difference`). That M "is the excursion costing one
  factor of e" is a theorem, not a convention.
- **EXTERNAL + STRUCTURAL (necessary bound):** requiring the screening length
  1/m = √(8π)(M/M_Pl)Λ^{−1/2} to exceed the horizon c/H₀ gives, recomputed under my
  own hand from Planck 2018 (Ω_Λ=0.6889, H₀=67.66): Λ=1.10560e-52 m⁻²,
  Λ^{−1/2}=9.5104e25 m, c/H₀=1.3672e26 m, √(8π)=5.0133, so
  **M/M_Pl ≥ 0.28676 ∈ (1/4, 1/3)** (`horizon_requires_planckian_scale`,
  `required_ratio_is_near_one`); monotone in M (`screening_length_strictly_monotone`).
- **This bound is OBSERVATIONAL, not substrate-derived.** It is
  (c/H₀)·Λ^{1/2}/√(8π) — H₀ and Λ are measured; √(8π) is geometry. The substrate
  supplies none of it. (A dimensionless ratio like M/M_Pl is exactly the kind of
  thing a substrate *with dynamics* could fix — but here the only constraint on it
  is observational, and even that is a bound, not a value.)
- **EXTERNAL upper bound:** the swampland distance conjecture bounds ΔΦ ≲ O(1) M_Pl,
  giving a window M/M_Pl ∈ [0.287, ~1] — factor ~3.5, no value inside.
- **Verdict:** substrate does NOT fix M. It fixes M's structural role. The value is
  squeezed by (mechanism + observed Λ + swampland) into a factor-~3 window near M_Pl.

### f — the ch₂–φ coupling (1/f)∫φ·ch₂ (axion decay constant)

- **STRUCTURAL (Lean, LambdaEffFromAction step 0):** of the five objects the corpus
  calls ch₂, the covariant local action admits only the **Pontryagin density
  Tr(F∧F)** (a top form). That is a selection fact about the action.
- **CORRECTION to the first draft:** I wrongly wrote "f couples to a charge
  quantized in ℤ[1/3] units." That conflates three distinct objects — the local
  Pontryagin *density* (a continuous 4-form, not quantized), its *integral* over a
  closed 4-manifold (the instanton number, in ℤ), and the substrate's K₀=ℤ[1/3].
  Integrated-charge quantization does not quantize the local density the action
  uses, and the instanton ℤ is not shown to be the substrate's ℤ[1/3] channel.
  Retracted.
- **NOT fixed:** f's value (a dimensionful decay constant). No Lean/chapter derives
  it; its ratio to M_Pl is likewise not supplied — not forbidden, just absent.
- **Verdict:** substrate fixes only which ch₂ the action admits, not f.

### ch₂(a) — the cosmic source history

- **STRUCTURAL:** ch₂ is bounded — entanglement form 1−Tr(ρ²) ∈ [0,1]; Pontryagin
  form a continuous density. That is all the construction pins.
- **OPEN (the locus of all fitting freedom):** the profile ch₂(a) — which sets the
  DE history w(a) — is derived nowhere (no Lean, no chapter). A function of the
  dimensionless a is NOT forbidden to the substrate; it is simply not supplied,
  because the construction has no evolution law for the source. Any H(z) prediction
  inherits that freedom.
- **Verdict:** ch₂(a) is undetermined by the current construction.

## The upstream issue this exposes (repair, not disclosure)

The ch₂ the covariant action admits is the **Pontryagin density Tr(F∧F)** (gauge
topology). The ch₂ carrying the *consciousness* reading, and the one the churn/EEG
test measures, is the **linear entropy 1−Tr(ρ²)**. These are distinct objects (step
0 lists them separately). So, as written, the mechanism proves "a gauge-topological
density sources φ ⇒ Λ_eff falls" — NOT "consciousness sources dark energy." The
consciousness reading requires a *defined map* from the density-matrix entropy to
the gauge Pontryagin class **and a proof** that it holds. Until that bridge exists,
the dark-energy mechanism and the consciousness claim are two theorems sharing a
symbol. This is an identification to prove (or the mechanism to be stated without
the consciousness label) — an upstream repair, not a caveat.

## What would actually close any one of the three (what a completion owes)

- M: a dynamical principle selecting a point in [0.287, 1] M_Pl (currently only the
  window exists), or a derivation of the dimensionless ratio M/M_Pl.
- f: a dimensionful completion of the substrate that carries a scale, plus the
  coupling's value — neither present.
- ch₂(a): evolution equations + initial/boundary conditions for the source (this is
  the "dynamics" the construction lacks), and/or the Pontryagin↔entropy bridge above.

## Provenance / labels
- PROVEN (kernel): K₀=ℤ[1/3]; σ-table; substrate rigidity + unique trace. (These
  prove the α-ratio fact and the substrate's structure — NOT an impossibility for
  the DE parameters; see "Answer, first".)
- STRUCTURAL (Lean, [propext,Classical.choice,Quot.sound]): lambda_eff_* /
  suppression_* / yukawa_* / horizon_* — shape + the necessary M-bound, not values.
- EXTERNAL (cited, not derived here): Planck 2018 (H₀, Ω_Λ); swampland distance
  conjecture; Noether/Bianchi/PPN.
- OPEN: values of M, f; ratio M/M_Pl; the function ch₂(a); the Pontryagin↔entropy
  identity; and any dynamics that would fix the ratios/profile.

## Note on σ(√2π)
σ(√2π) ≈ −0.0387 < 0 is what *disqualifies* the R_f(√2π) kernel (it stays bounded
where a 3-D Green's function must diverge), so R_f was *replaced* by the Yukawa
kernel e^{−mr}/4πr. σ(√2π) therefore does not enter the corrected mechanism and sets
none of M, f, ch₂(a).

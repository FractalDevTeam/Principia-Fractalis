# Can the substrate fix M, f, ch₂(a)? — the dark-energy parameters, 2026-10-11

Author: Pablo Cohen. Task: derive the three undetermined parameters of PF's
Λ_eff dark-energy mechanism (ch08) — M, f, ch₂(a) — from the substrate.
Verified under my own hand; four-label ledger (PROVEN / STRUCTURAL / EXTERNAL / OPEN).

## Answer, first

The substrate does **not** fix M, f, or ch₂(a) — and this is not a gap to be
filled later. It is **forced** by the same obstruction already PROVEN for the
α-values: the substrate is a *dimensionless* C*-algebra whose only invariant
channel is K₀(T_∞) = ℤ[1/3] (`pi_not_ktheoretic_ratio`). A dimensionless algebra
with a ℤ[1/3] invariant channel cannot emit a dimensionful energy scale (M or f
in GeV) or a free function (ch₂(a)). What the substrate DOES fix is the *structure*
of all three; what it cannot fix is their *values*. Naming exactly which external
inputs the values require is the precision result, and it locates the
program→TOE boundary precisely at the dark-energy sector.

Consequence that holds the line: **the quantitative DESI test cannot be run from
the substrate alone without choosing ch₂(a) — i.e. without fitting.** So the DESI
status stays what the prior note set it to: retrospective qualitative
compatibility, not a quantitative confirmation.

## The three parameters, structure vs value

### M — field-excursion scale in V(φ) = (Λ₀/κ)e^{−φ/M}

- **STRUCTURAL (Lean):** M is the *sole* scale in the exponential — the
  suppression depends only on (ψ−φ)/M, no hidden second scale
  (`suppression_factor_is_scaled_difference`). That M *is* "the excursion costing
  one factor of e" is a theorem, not a convention.
- **EXTERNAL + STRUCTURAL (necessary bound):** requiring the screening length
  1/m = √(8π)(M/M_Pl)Λ^{−1/2} to exceed the horizon c/H₀ gives, recomputed under
  my own hand from Planck 2018 (Ω_Λ=0.6889, H₀=67.66): Λ=1.10560e-52 m⁻²,
  Λ^{−1/2}=9.5104e25 m, c/H₀=1.3672e26 m, √(8π)=5.0133, so
  **M/M_Pl ≥ 0.28676 ∈ (1/4, 1/3)** (`horizon_requires_planckian_scale`,
  `required_ratio_is_near_one`). Monotone in M (`screening_length_strictly_monotone`),
  so it is a genuine threshold.
- **The number 0.287 is observational, not substrate-derived.** It is
  (c/H₀)·Λ^{1/2}/√(8π) — H₀ and Λ are measured; √(8π) is geometry. The substrate
  contributes the logical structure, not the value.
- **Window, not a value:** the swampland distance conjecture (EXTERNAL, cited)
  bounds field excursions at ΔΦ ≲ O(1) M_Pl, giving M/M_Pl ∈ [0.287, ~1] — a
  factor of ~3.5, pinned entirely by observation + EFT, with **no substrate value
  inside it**.
- **Verdict:** substrate does NOT fix M. It fixes M's role. The value is squeezed
  by (mechanism + observed Λ + swampland) into a factor-~3 window near M_Pl.

### f — the ch₂–φ coupling (1/f)∫φ·ch₂ (axion decay constant)

- **STRUCTURAL (Lean, LambdaEffFromAction step 0):** of the five objects the
  corpus calls ch₂, exactly one can sit in a covariant local action — the
  **Pontryagin density Tr(F∧F)**, already a top form, so φ·ch₂ is the standard
  axion coupling. The Pontryagin integral is *topologically quantized*, and
  K₀(T_∞)=ℤ[1/3] is the substrate receptacle for that charge. So the substrate
  fixes that **the source is a topological charge quantized in ℤ[1/3] units** —
  it fixes the *kind* of thing f multiplies.
- **NOT fixed:** f's *scale* (f in GeV). f is a dimensionful decay constant; the
  dimensionless algebra cannot emit it, and no Lean file or chapter derives it
  (verified: targeted grep for a decay-constant/coupling value returns empty).
- **Verdict:** substrate fixes f's structural role (coupling to a quantized
  topological charge), not its value.

### ch₂(a) — the cosmic source history

- **STRUCTURAL:** ch₂ is bounded — entanglement form 1−Tr(ρ²) ∈ [0,1]; Pontryagin
  form quantized. That is all the substrate pins.
- **OPEN (the locus of all fitting freedom):** the profile ch₂(a) as a function
  of scale factor — which is exactly what sets the DE history w(a) — is derived
  nowhere (no Lean, no chapter; grep empty). It is a free function. Any H(z)
  prediction inherits that freedom, so a w₀–w_a contour "fit" would be fitting it.
- **Verdict:** ch₂(a) is undetermined by the substrate.

## The upstream issue this exposes (repair, not disclosure)

The ch₂ that the covariant action admits is the **Pontryagin density** (gauge
topology). The ch₂ that carries the *consciousness* reading — and the one the
empirical churn/EEG test measures — is the **linear entropy 1−Tr(ρ²)**. Step 0
lists these as *different* objects. So, as written, the action derivation gives
"a topological-charge density sources φ ⇒ Λ_eff decreases", NOT "consciousness
sources dark energy." The consciousness reading of the mechanism requires a
*separate proof* that the ch06 consciousness invariant equals (or is controlled
by) the gauge Pontryagin class. Until that identification is made, the
dark-energy mechanism and the consciousness claim are two different theorems that
happen to share the symbol ch₂. **This is an upstream identification to prove (or
to state the mechanism without the consciousness reading), not merely a caveat.**

## What would actually close any one of the three (what a TOE-completion owes)

- M: one dimensionful bridge (fix M_Pl as THE scale) + a reason the excursion
  lands at a specific point in [0.287, 1] M_Pl — currently only the window exists.
- f: a derivation of the axion decay constant from a dimensionful completion of
  the substrate (an embedding that carries a scale), which the substrate as a
  pure C*-algebra does not have.
- ch₂(a): either (i) a dynamical law for the source over cosmic time, or
  (ii) the Pontryagin↔consciousness identification above plus a cosmic model of
  that invariant. Both are open.

## Provenance / labels
- PROVEN (kernel): K₀=ℤ[1/3] obstruction; σ-table; substrate rigidity + unique trace.
- STRUCTURAL (Lean, [propext,Classical.choice,Quot.sound]): all lambda_eff_* /
  suppression_* / yukawa_* / horizon_* theorems — they carry shape + the necessary
  M-bound, not values. Cosmological inputs are external/cited.
- EXTERNAL (cited, not derived here): Planck 2018 (H₀, Ω_Λ); swampland distance
  conjecture; Noether/Bianchi/PPN.
- OPEN: values of M, f; the function ch₂(a); the Pontryagin↔consciousness identity.

## Note on σ(√2π)
Correcting an earlier overstatement: σ(√2π) ≈ −0.0387 < 0 is what *disqualifies*
the R_f(√2π) kernel (it stays bounded where a 3-D Green's function must diverge),
so R_f was *replaced* by the Yukawa kernel e^{−mr}/4πr. σ(√2π) therefore does
**not** enter the corrected mechanism and sets none of M, f, ch₂(a).

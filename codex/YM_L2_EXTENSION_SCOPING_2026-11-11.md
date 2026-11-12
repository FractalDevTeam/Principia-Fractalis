# YM reflection positivity — L² extension scope (2026-11-11)

**Target:** extend `wilson_reflection_positivity_of_continuous` (r385, 2026-10-29)
from **continuous** test functions to **L²** test functions.

**Head at write time:** `fe3ba338` on `origin/master`.

## What the deployed theorem says

`wilson_reflection_positivity_of_continuous (hL : Even L) (β : ℝ) (F : Fin K → GaugeField L → ℂ) (hF_support) (hF_cont)` concludes the K×K matrix

   `∫ star(F_i(θU)) · F_j(U) ∂μ_Gibbs`

is `PosSemidef`. On three-axiom bar. The lane's acceptance criterion
was "empty hypothesis list, kernel-clean" — current state has `Even L`,
support in `Λ_+ ∪ Λ_0`, and Continuous. The L² extension removes
Continuous.

## Why remove Continuous

OS reconstruction and the physical Hilbert space both live on `L²`,
not on `C(GaugeField)`. The RP statement without continuity is the
form all downstream quantum-field work uses.

## Five-step plan (deliverable-by-deliverable)

### Step 1 — Cauchy-Schwarz bound on Gram entries

**Target lemma:**
```
∀ F G : GaugeField L → ℂ, (MemLp F 2 μ_Gibbs) → (MemLp G 2 μ_Gibbs) →
  ‖∫ star(F(θU)) · G(U) ∂μ_Gibbs‖
    ≤ (∫ ‖F U‖² ∂μ_Gibbs)^(1/2) · (∫ ‖G U‖² ∂μ_Gibbs)^(1/2)
```

**Proof ingredients (all in mathlib):**
- `norm_integral_le_integral_norm` (triangle)
- Pointwise `‖star z · w‖ = ‖z‖·‖w‖` (direct)
- `integral_mul_le_Lp_mul_Lq_of_nonneg` + `HolderConjugate.two_two`
- `MemLp.norm` to lift `MemLp F 2 → MemLp ‖F‖ 2`
- `MemLp.comp_measurePreserving` + `wilsonGibbsMeasure_measurePreserving_timeReflection` (just landed) to lift `MemLp F → MemLp (F ∘ θ)`
- `integral_norm_sq_wilsonGibbs_timeReflection` (just landed) for the final isometry rewrite.

**Estimated size:** 40–60 Lean lines.

### Step 2 — Gibbs θ-invariance ★ DONE 2026-11-11 ★

`wilsonGibbsMeasure_measurePreserving_timeReflection` + 4 corollaries, in
`PF/YangMills/WilsonGibbsMeasurePreserving_2026_11_11.lean`. See commits
`90e78fea` + `fe3ba338`.

### Step 3 — Density of continuous in `L²(supportedOnPlusZero)`

**Target lemma:** for any `F : GaugeField L → ℂ` with `MemLp F 2 μ_Gibbs` and
`supportedOnPlusZero F`, there exists a sequence `F_n : GaugeField L → ℂ`
each continuous AND `supportedOnPlusZero`, converging to F in L².

**Key subtlety:** mathlib has `MemLp.exists_boundedContinuous_eLpNorm_sub_le`
for density of bounded continuous in L² on nice measure spaces, but does
NOT preserve specific support conditions. Need to do mollification-style
argument that respects `supportedOnPlusZero`.

Since `supportedOnPlusZero F` means F factors through the restriction to
`Λ_+ ∪ Λ_0`, and the lattice is finite, this is (modulo bookkeeping) just
"continuous dense in L² on the finite-dimensional compact Lie group
`SU(2)^{Λ_+ ∪ Λ_0}`". Mathlib has continuous-dense-in-L² on compact
Hausdorff; the support-factoring is additive.

**Estimated size:** 80–150 Lean lines. The non-trivial part is naming the
restriction map and pushforward measure correctly.

### Step 4 — `Matrix.PosSemidef` closed under entrywise L² limit

For a sequence of K×K complex matrices `M_n` with each `M_n` PosSemidef and
entrywise `M_n i j → M i j`, conclude `M` is PosSemidef.

Direct: `PosSemidef M ↔ M = M* ∧ ∀ v, 0 ≤ v*Mv`. Hermiticity is preserved
under entrywise limits (continuous conjugation + finitely many entries).
Quadratic form: `v*M_n v → v*Mv` (bilinear + finite K), and limit of
non-negatives is non-negative.

**Estimated size:** 30–50 Lean lines. Standard.

### Step 5 — Assembly

Given `F : Fin K → GaugeField L → ℂ` with each `F_i` in `L²` and supported:
1. Build approximating sequence of continuous `F_i,n` (step 3).
2. Each Gram matrix of `F_·,n` is PosSemidef (deployed r385).
3. Gram entries converge in L²-topology (step 1 + step 2).
4. PSD is closed under entrywise limit (step 4).
5. Conclude `Gram F` is PosSemidef.

**Estimated size:** 30–60 Lean lines.

## Total estimate for L² extension

~200–320 Lean lines across 4 new files (plus the scoping doc).

**Time estimate:** 1–2 dedicated sessions of focused work.

## Priority within the broader Millennium lane

Per `codex/MILLENNIUM_STATUS_2026-11-11.md`:

1. YM extend RP to L² — this lane
2. BSD scoping A (second rank-0 via not_fermat_42_sub)
3. NS Young's L¹⋆L² → L²
4. RH re-examine c=829/64 wall
5. BSD scoping B.rank≤1 (full Selmer)

Step 2 of this scope is now done. Starting with step 1 (CS bound) is the
natural next action — it uses only existing mathlib + the just-landed
Gibbs-invariance lemmas.

## Deployed state after 2026-11-11

Files:
- `PF/YangMills/WilsonRPCorollaries_2026_11_11.lean` — 4 sesquilinear
  forms of r385 (hermitian, scalar PSD, scalar .re ≥ 0, scalar .im = 0)
- `PF/YangMills/WilsonGibbsMeasurePreserving_2026_11_11.lean` — 5 theorems
  for step 2 (Gibbs MP + measurable embedding + 3 integral invariances)

Both three-axiom bar. Collectively: **step 2 of the L² extension is live.**

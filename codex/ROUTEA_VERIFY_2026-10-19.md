# NS Route A verification: all ten "should exist" confirmed, both phantoms confirmed — but **two items marked "must fail" actually exist**, and the plan changes

**Date:** 2026-10-19 (Legion, probe elaborated on Acer). Verification, not
building. Labels **FACT** (elaborated) / **JUDGEMENT** / **OPEN**.
Probe: `codex/routeA_probe.lean`, run with `lake env lean` against
`import Mathlib` — so it is authoritative over the **whole** library, not just
what PF imports.

---

## HEADLINE

**Two of the three items the analysis expected to fail are present**, and both
are load-bearing:

1. **`ContinuousLinearMap.extend` EXISTS.** It is exactly
   bounded-extension-by-density. Route A's hand-rolled extension machinery is
   **unnecessary**.
2. **`InnerProductSpace ℂ (Lp ℂ 2 volume)` SYNTHESISES**, via
   `L2.innerProductSpace`. The R4 blocker as stated is **not a blocker**.

Both phantoms the analysis predicted are indeed phantoms, so §7's instinct was
sound — it was wrong in the direction of pessimism, not optimism.

---

## 1. "Should exist" — 10/10 CONFIRMED PRESENT. FACT

| # | declaration | status |
|---|---|---|
| 1 | `SchwartzMap.toLp` | ✅ `SchwartzSpace.lean:1304` |
| 2 | `SchwartzMap.memLp` | ✅ |
| 3 | `SchwartzMap.norm_toLp` | ✅ |
| 4 | `SchwartzMap.injective_toLp` | ✅ |
| 5 | `MeasureTheory.Lp.simpleFunc.dense` | ✅ |
| 6 | `SchwartzMap.fourierTransformCLM` | ✅ |
| 7 | `SchwartzMap.fourierTransformCLE` | ✅ |
| 8 | `UniformSpace.Completion.extension` | ✅ (+ `extension_unique`) |
| 9 | `Submodule.orthogonalProjection` | ✅ (also `Submodule.starProjection`) |
| 10 | `MeasureTheory.convolution` | ✅ (as `convolution`, notation `⋆[L, μ]`) |

Two spelling notes: the **root** `orthogonalProjection` is absent — it must be
written `Submodule.orthogonalProjection`. And `convolution` is root-level, not
under `MeasureTheory`, though it resolves through the `open`.

## 2. "Must fail" — one of three. FACT

| # | declaration | predicted | actual |
|---|---|---|---|
| 11 | `SchwartzMap.denseRange_toLp` | phantom | ✅ **ABSENT — phantom confirmed** |
| 12 | `LinearMap.extendOfNorm` | phantom | ✅ **ABSENT — phantom confirmed** |
| 13 | `ContinuousLinearMap.extend` | phantom | ❌ **EXISTS** |

### 13 is the finding. FACT, type elaborated

```
@ContinuousLinearMap.extend :
  (E →SL[σ₁₂] F) → [CompleteSpace F] →
    (e : E →L[R] Fₗ) → DenseRange ⇑e → IsUniformInducing ⇑e → Fₗ →SL[σ₁₂] F
```

Read it: **given a bounded map on a dense uniformly-inducing image, extend it to
the whole space, continuously.** That is the entire content Route A was going to
hand-roll via `LinearMap.extendOfNorm` (which does not exist) or
`UniformSpace.Completion.extension` (which does, but makes you build the
completion and transport across it).

**JUDGEMENT: this collapses a step rather than easing one** — the hand-rolled
extension work goes away. **But NOT with `e := toLpCLM`, and this is the
subtlety that matters.** FACT, from the source:

```
norm_toLp : ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ)          -- :1310
norm_toLp_le_seminorm : ∃ k C, 0 ≤ C ∧ ∀ f, ‖f.toLp p μ‖ ≤ C * (… seminorm …) f  -- :1319
```

`toLp` preserves the **Lᵖ** norm of the *function*, but the Schwartz space
carries the seminorm-family topology, which is **strictly finer** than the `Lᵖ`
norm — the second lemma says the map is merely *bounded by* a Schwartz seminorm.
So `toLpCLM` is continuous and **is not uniformly inducing**, and `extend`'s
`IsUniformInducing ⇑e` hypothesis would be **false**. My first reading of this
was wrong and I am correcting it before it reaches the build.

**The correct instantiation** takes `e` to be the inclusion of the *range as a
submodule of `L²`*, not the Schwartz map:

* `Submodule.subtypeL` ✅ present — the inclusion as a CLM;
* `Isometry.isUniformInducing` ✅ present, and
  `IsUniformEmbedding.isUniformInducing` ✅ — so `IsUniformInducing` for a
  subspace inclusion is free, the subspace norm being the restriction;
* density then has to be proved for *that* inclusion (§4).

(The root `isUniformInducing_subtype_val` is absent; use the two above.)

Three further routes exist if this one's side conditions bite:
`ContinuousLinearMap.extendTo𝕜`, `IsDenseInducing.extend`,
`LinearIsometry.extend` — all present. And **`SchwartzMap.toLpCLM` exists**
(`:1332`), so the CLM packaging of `toLp` is free even though it is not the `e`
for `extend`.

## 3. "Verify" — one passes, one is genuinely absent

### 14. `InnerProductSpace ℂ (Lp ℂ 2 volume)` — **SYNTHESISES.** FACT

`#synth` resolved it to **`L2.innerProductSpace`**. The expectation that this
fails (R4) is wrong.

**JUDGEMENT:** whatever R4 was blocking on, it is not the absence of the inner
product structure on `L²`. If R4 has a real obstruction it is somewhere else and
needs re-stating; as written, this line of the analysis is simply not a
blocker. **OPEN: I did not read R4 itself** — only the claim about it in the
brief — so I cannot say what the real obstruction is, only that this one is not it.

### 15. L¹⋆L² Young inequality — **ABSENT, and absent in substance.** FACT

Absent under all five probed names
(`eLpNorm_convolution_le`, `enorm_convolution_le`, `convolution_mem_Lp`,
`MemLp.convolution`, `eLpNorm_convolution_le_eLpNorm_mul_eLpNorm`).

And not merely a naming miss — three independent checks:

* **no declaration anywhere in mathlib** matches `convolution` together with
  `MemLp` or `eLpNorm`;
* `Analysis/Convolution.lean`'s only integrability result is
  **`Integrable.integrable_convolution : Integrable f → Integrable g →
  Integrable (f ⋆[L, μ] g)`** — the `p = 1` case, L¹⋆L¹→L¹;
* "Young" in mathlib is **only** Young tableaux (`Combinatorics/Young/`); there
  is no Young convolution inequality at all.

**So L¹⋆L² → L² must be built.** It is the one genuine new-mathematics item on
this list.

## 4. The phantom's *fact* is also missing — and this is the real gap. FACT

`SchwartzMap.denseRange_toLp` being a phantom would be harmless if the density
were available under another name. **It is not.** Neither
`Analysis/Distribution/SchwartzSpace.lean` nor `FourierSchwartz.lean` contains
any `dense`/`denseRange` result, and no file mentioning `SchwartzMap` carries
one.

**JUDGEMENT: this is Route A's actual load-bearing gap**, and it is sharper than
the brief suggests. `ContinuousLinearMap.extend` demands
`DenseRange ⇑e` as a *hypothesis* — so the step the analysis thought it needed
(`extendOfNorm`) is free, and the step it recorded as a mere phantom
(`denseRange_toLp`) is the thing that must actually be proved. **The gap moved,
it did not disappear.**

Route A therefore needs exactly two new facts:

1. **Schwartz dense in `L²`** — concretely `DenseRange ⇑(S.subtypeL)` for `S`
   the range submodule (equivalently `DenseRange ⇑(toLpCLM 2 volume)`; the two
   are the same set-level statement, and it is the submodule form that `extend`
   consumes, per §2). Available ingredient: `Lp.simpleFunc.dense` (present), so
   the standard route is simple functions dense in `Lp`, then approximate simple
   functions by Schwartz. **Not built, and not in mathlib.**
2. **L¹⋆L² → L²** (§3.15).

## 5. Verdict

**The spec is sound but mis-priced in both directions.** Ten of ten "should
exist" are real; two phantoms are real phantoms; but the extension step is free
and the `L²` inner product is free, while the density fact and the Young
inequality are the two things that must be built.

**The plan changes as follows. JUDGEMENT:**

* **delete** the hand-rolled extension work — call `ContinuousLinearMap.extend`,
  but with `e` the **range submodule's inclusion** (`Submodule.subtypeL`), *not*
  `toLpCLM`, whose source topology makes `IsUniformInducing` false (§2);
* **delete** whatever R4 contingency rested on `L²` lacking an inner product;
* **promote** `DenseRange toLpCLM` from "phantom, note it" to a first-class
  build item — it is now a *hypothesis of the tool we are using*;
* **keep** L¹⋆L² as the one genuine new-mathematics item.

**Net: two items off the build, one promoted onto it, one unchanged.** Whether
that shortens Route A overall I cannot say without the §7 line items — **OPEN,
and the Acer should re-price before building.**

---

## Label summary

* **FACT (elaborated, not grepped):** every present/absent verdict above, from a
  `#check`/`#synth` probe over `import Mathlib`; the printed type of
  `ContinuousLinearMap.extend`; `#synth` resolving to `L2.innerProductSpace`;
  the `SchwartzSpace.lean:1304/1332` locations; the absence of any
  `convolution`×`MemLp`/`eLpNorm` declaration, of any Young convolution
  inequality, and of any Schwartz density result.
* **JUDGEMENT (mine):** that `extend` collapses rather than eases the extension
  step; that the gap "moved rather than disappeared" onto `DenseRange`; the four
  plan changes.
* **OPEN / NOT established:** I did not read R4 itself, only the brief's claim
  about it, so I can say the inner-product obstruction is absent but not what
  R4's real obstruction is; I have not re-priced Route A, having no §7 line
  items; and I have **not** verified that the range of `toLp` is a *submodule*
  in the form `extend` wants (i.e. that the obvious `Submodule` packaging of
  `Set.range (toLpCLM …)` is available or cheap) — that is the next probe, and
  it is the last thing standing between §2's corrected plan and a build.

### A correction I made to myself before shipping

My first pass concluded "call `extend` with `e := toLpCLM`". That is **wrong** —
`IsUniformInducing ⇑toLpCLM` is false, because the Schwartz topology is strictly
finer than the `L²` norm (`norm_toLp_le_seminorm` is a *bound by a seminorm*,
not an isometry). Caught by probing `extend`'s second hypothesis, which I had
listed as an open item and then closed rather than shipping it open. The tool
still applies and the step still collapses — but through a submodule inclusion,
not the Schwartz map. **A verification report that gets the instantiation wrong
is worse than one that says "unverified".**

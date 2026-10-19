# Route A spec update: `extend` assembles — the chain is verified end to end. But the gap is THREE items, not two: `e2dcba22` folded the operator-side step invisibly

**Date:** 2026-10-19 (Legion, probes elaborated on Acer). Analysis only.
Labels **FACT** (elaborated) / **JUDGEMENT** / **OPEN**.
This is the **delta** over `codex/ROUTEA_VERIFY_2026-10-19.md` (`e2dcba22`),
which already answered Rio's questions 1–4; read that first. Everything below
is new.

---

## 1–2. The two, and whether they serve Route A. FACT, from `e2dcba22`

| marked "must fail" | actual |
|---|---|
| `ContinuousLinearMap.extend` | **EXISTS** — `(E →SL[σ₁₂] F) → [CompleteSpace F] → (e : E →L[R] Fₗ) → DenseRange ⇑e → IsUniformInducing ⇑e → Fₗ →SL[σ₁₂] F` |
| `InnerProductSpace ℂ (Lp ℂ 2 volume)` | **SYNTHESISES**, via `L2.innerProductSpace` |

`e2dcba22` §2 already corrected my first reading: **`extend` cannot take
`e := toLpCLM`**, because `norm_toLp_le_seminorm` is a *bound by a Schwartz
seminorm*, not an isometry — the Schwartz topology is strictly finer than the
`L²` norm, so `IsUniformInducing ⇑toLpCLM` is **false**. The correct `e` is a
submodule inclusion.

## 3. The assembly now verified to close. FACT — this is new

`e2dcba22` asserted the submodule route and left as OPEN *"whether the range of
`toLp` is available as a `Submodule` in the form `extend` wants — the next
probe, and the last thing standing between the corrected plan and a build."*
**Probed; it closes.** With `S : Submodule ℂ (Lp ℂ 2 volume)` the range:

| `extend` needs | supplied by | status |
|---|---|---|
| `e : ↥S →L[ℂ] L²` | `Submodule.subtypeL` | ✅ |
| `IsUniformInducing ⇑e` | `(S.subtypeₗᵢ).isometry.isUniformInducing` | ✅ **chain verified** — all three present |
| `DenseRange ⇑e` | — | ❌ **build item (§4.1)** |
| `[CompleteSpace F]` | `L²` is complete | ✅ free |
| `f : ↥S →SL[σ] F` | — | ❌ **build item (§4.2)** |

Density has a stating route too: `Submodule.dense_iff_topologicalClosure_eq_top`
and `Submodule.topologicalClosure_eq_top_iff` are both present, as is
`Submodule.topologicalClosure`.

### Four near-misses that will waste a build cycle. FACT

| wrong name (ABSENT) | use instead |
|---|---|
| `LinearIsometry.isUniformInducing` | `Isometry.isUniformInducing` ∘ `LinearIsometry.isometry` |
| `ContinuousLinearMap.range` | `LinearMap.range` on the coerced linear map |
| `ContinuousLinearMap.domRestrict` | `.comp S.subtypeL` — there is **no** domain-restriction shortcut |
| `Submodule.subtypeₗᵢ_norm` | go through `subtypeₗᵢ`'s isometry directly |

(Also from `e2dcba22`: the root `orthogonalProjection` and
`SchwartzMap.denseRange_toLp` are absent; `convolution` is root-level.)

## 4. The exact gap — THREE items. JUDGEMENT, and item 2 is new

`e2dcba22` named two. Probing the assembly surfaced a third that I had folded
invisibly into "call `extend`", and it is the one with real analytic content.

1. **Schwartz dense in `L²`** — `DenseRange ⇑(S.subtypeL)`. Not in mathlib
   under any name (`e2dcba22` §4: no `dense`/`denseRange` result in
   `SchwartzSpace.lean` or `FourierSchwartz.lean`, and no file mentioning
   `SchwartzMap` carries one). Ingredient present: `Lp.simpleFunc.dense`.
   **Promoted from "phantom, note it" to a hypothesis of the tool.**

2. **The operator as a CLM on the subspace — NEW.** `extend` wants
   `f : ↥S →SL[σ] F`: the operator **already defined on the submodule of `L²`,
   bounded in the `L²` norm**. A Schwartz-defined operator is not that object.
   Two sub-steps:
   * *well-definedness* — the output's `L²` class must depend only on the
     input's `L²` class. Transportable via `SchwartzMap.injective_toLp`
     (present ✅).
   * ***`L²`-boundedness on Schwartz*** — `‖Tf‖_{L²} ≤ C‖f‖_{L²}`. **This is
     the actual analytic content of Route A and it is not a library lookup.**
     `ContinuousLinearMap.domRestrict` being absent means there is no shortcut
     around constructing it.

3. **L¹⋆L² → L²** — unchanged from `e2dcba22` §3.15: absent in substance, not
   just in name (nothing in mathlib pairs `convolution` with `MemLp`/`eLpNorm`;
   the only result is `Integrable.integrable_convolution`, the `p = 1` case; and
   "Young" in mathlib is Young *tableaux*).

### Net effect on the plan. JUDGEMENT

**Cheaper than DeepSeek's spec, but not as cheap as `e2dcba22` implied.** Off
the build: the hand-rolled extension, and any R4 contingency resting on `L²`
lacking an inner product. Onto it: the density fact. Unchanged: L¹⋆L². **And now
explicit rather than hidden: the operator's `L²`-boundedness**, which was always
going to be the work and which no amount of library archaeology removes.

**So the honest summary is that the library gives Route A its *plumbing* for
free and none of its *analysis*.** `extend` saves the extension boilerplate;
it does not save proving the operator bounded, and it demands the density fact
as a hypothesis.

---

## Label summary

* **FACT (elaborated):** `extend`'s and the instance's existence (from
  `e2dcba22`); the presence of `Submodule.subtypeL`, `Submodule.subtypeₗᵢ`,
  `LinearIsometry.isometry`, `Isometry.isUniformInducing`, `LinearMap.range`,
  `Submodule.topologicalClosure` and both density-characterisation lemmas; the
  absence of the four near-miss names.
* **JUDGEMENT:** that the gap is three items rather than two, and that item 2 is
  the analytic core; that the library supplies plumbing and not analysis.
* **OPEN / NOT established:** I have not written the `extend` application even
  as a skeleton, so "the chain closes" is a check that every *hypothesis* has a
  supplier, not that they compose without friction; I still have not read R4
  itself; and the `L²`-boundedness in item 2 is unpriced — it depends entirely
  on which operator Route A is extending, which §7 names and I do not have.

# PRINCIPIA FRACTALIS — α-SKELETON STRUCTURAL-LAW PROVENANCE AUDIT

**Date:** 2026-08-24
**HEAD:** `22c55e57b51b0638e9bb516761e74e085415ba00` (post-intrinsic-origin audit on `origin/master`)
**Companion to:** `codex/ALPHA_SKELETON_INTRINSIC_ORIGIN_AUDIT_2026-08-24.md`
**Deliverable:** the READ-ONLY structural-law provenance audit mandated by the post-intrinsic-origin directive. No mathematical definitions modified. No new proof wrappers created. No theorem attack started.

The question this document answers:

> The prior audit established that the α-values themselves have effective seed dimension 1 given the **eight structural laws** {L1, L2, L3, L4, L5, I6, I7, I9}. This audit interrogates the eight laws themselves.
>
> **For each of L1–L5, I6, I7, I9: is it an intrinsic PF theorem, an external classical theorem, a target-encoded assumption chosen because the assigned α-values happen to satisfy it, a trivial arithmetic identity, or an unsupported narrative gap?**

The intent is to distinguish laws that are genuine substrate consequences from laws that are algebraic residues of the α-*definitions* themselves.

---

## 1. HEAD

`22c55e57b51b0638e9bb516761e74e085415ba00`

## 2. The eight laws as they appear in the kernel

From `PF_Lean4_Code/PF/AlphaSkeletonUniqueness_r128.lean:110–128`:

```lean
structure StructuralLaws (s : AlphaSkeleton) : Prop where
  hodge_minpoly : s.aHodge * s.aHodge = s.aPoincare * s.aHodge + s.aPoincare   -- L1
  ym_shift      : s.aYM = s.aPoincare + 1                                       -- I7
  p_norm        : s.aP * s.aP = s.aYM                                           -- L2
  rh_prod       : s.aRH * s.aYM = 3                                             -- I9
  np_trace      : s.aPoincare + 2 * (s.aNP - s.aHodge) = s.aRH                  -- L3
  qg_norm       : s.aQG * s.aQG = s.aYM * Real.pi                               -- L4
  ns_scaling    : s.aNS = s.aRH * Real.pi                                       -- L5
  bsd_gauge     : s.aNS = s.aYM * s.aBSD                                        -- I6
```

The r128 §5 backward-anchor variant (`alpha_skeleton_unique_from_BSD`, line 327) uses the same eight laws.

## 3. Provenance classification scheme

Extending the A–G scheme from the intrinsic-origin audit with one new bucket:

| Code | Meaning |
|---|---|
| **A** | Intrinsic PF theorem: kernel-proved from substrate data without invoking any α-value in the hypotheses. |
| **B** | Conditional: kernel-proved but only under an unresolved auxiliary hypothesis. |
| **C** | Post-hoc rigidity of assigned values: the equation *holds* for the assigned α's, but its role in the corpus is to state their algebraic relationships rather than to force them. |
| **D** | Definitional: the equation unfolds `def α_X` on both sides and reduces to a mathlib identity. |
| **E** | Trivial arithmetic identity: kernel-proved by `norm_num` on numerical assignments alone (no substrate input). |
| **F** | Target-encoded: the equation's right-hand side was **chosen specifically because** the pre-declared α-values satisfy it; the equation would be false for any other consistent assignment. |
| **G** | Unsupported narrative: presented in prose as motivated by some substrate mechanism (Galois trace, scaling law, corpus invariant), but the mechanism has no kernel realization anywhere in the corpus. |
| **H** | External classical theorem: proved outside PF and cited (e.g. Perelman 2003, Wiles 1995). |

A single law may carry more than one code — F and G together capture "narrative dresses a target-encoded identity."

## 4. Table 1 — LAW-BY-LAW PROVENANCE

| # | Exact equation (LHS = RHS) | Kernel proof method on `canonical` | Provenance class | Target information inserted? | Independent of α-defs? | Depends on other laws? | Canonical PF object candidate | Exact missing bridge |
|---|---|---|---|---|---|---|---|---|
| **L1** | `α_Hodge² = α_Poincaré · α_Hodge + α_Poincaré` | `nlinarith [sq_sqrt5]` on `canonical.aHodge = (1+√5)/2` | **D + F** | YES — φ is the minimal polynomial of `α_Hodge := φ` by construction | NO — unfolds `α_Hodge := (1+√5)/2` and `α_Poincaré := 1` | Independent of other laws algebraically | `H3CoxeterOrigin` supplies `cos(π/5)=φ/2` intrinsically; substrate object `SymmetryGroup(base_3_substrate)` conjectural | **`Polynomial.minpoly ℚ φ = X² − X − 1`** proved and then bridged to an intrinsic PF-defined algebraic quantity — mathlib API `minpoly` never invoked in the corpus |
| **L2** | `α_P² = α_YM` | `sq_sqrt2` (mathlib `Real.mul_self_sqrt`) | **D + F** | YES — the equation is the minimal polynomial `x² − 2` of `α_P := √2` | NO — unfolds `α_P := √2` and `α_YM := 2` | Independent | Would require a **canonical order-2 element** in some PF-substrate algebra whose square is intrinsically 2 | **Not attempted anywhere.** No substrate operator's spectrum is proved to contain `√2`. |
| **L3** | `α_Poincaré + 2·(α_NP − α_Hodge) = α_RH` | `ring` after `rw [hPo, hRH, hHo]` in `forced_from_poincare` | **F** (also E under the identification `α_NP − α_Hodge = 1/4`) | YES — `α_NP := φ + 1/4` was **chosen** so this equation holds with `α_RH := 3/2` | NO — reduces to `1 + 2·(1/4) = 3/2` after unfolding | Uses α_Poincaré, α_NP, α_Hodge, α_RH values | The Galois-trace-on-coset-`φ+ℚ` narrative in the docstring at line 119 | The docstring calls this the "Galois trace law." Mathlib's `Algebra.trace ℚ ℚ(√5)` on `φ + q` gives `1 + 2q`, correct. But the trace equals `α_RH = 3/2` only because `q := α_NP − α_Hodge = 1/4` was inserted. **The bridge from the Galois trace to any substrate operator that *forces* `q = 1/4`** does not exist. |
| **L4** | `α_QG² = α_YM · π` | `Real.mul_self_sqrt (by positivity)` on `α_QG := √(2π)` | **D + F** | YES — the equation is the minimal polynomial `x² − 2π` of `α_QG := √(2π)` | NO — unfolds α-defs | Uses α_YM value | `SubstrateOscillator_r223` produces `π`-valued abscissae; combined with an `α_YM = 2` substrate origin could motivate `√(2π)` | Same shape as L2. No substrate operator's spectrum is proved to contain `√(2π)`. |
| **L5** | `α_NS = α_RH · π` | `ring` after `rw [hL.ns_scaling, hRH]` | **G** (with F on `canonical`) | YES — chosen so that `3π/2 = (3/2) · π` | NO on `canonical` — reduces to trivial identity. Symbolically the equation is what forces `α_NS` from `α_RH`. | Uses α_RH, α_NS values | **NONE identified in the corpus.** The docstring at line 124 calls it "π-scaling law" with no mechanism | **This is the load-bearing gap.** No substrate route from `α_RH` to `α_NS` via π-scaling exists. No corpus theorem justifies the multiplicative factor `π`. r124 (Gröbner) explicitly identified `α_BSD` as the free parameter of the 11-invariant system; L5 is the exact hidden equation that closes that freedom. |
| **I6** | `α_NS = α_YM · α_BSD` | `ring` (`3π/2 = 2 · (3π/4)`) | **E + F** | YES — coefficients chosen so `2 · (3π/4) = 3π/2` | NO | Uses α_NS, α_YM, α_BSD values | Corpus-cited as "gauge invariant" | Cited as a "corpus invariant" but never proved from a substrate gauge structure. **`GaugeInvariance` predicate exists in the corpus in name only.** |
| **I7** | `α_YM = α_Poincaré + 1` | `norm_num` (`2 = 1 + 1`) | **E + F** | YES — this is the arithmetic assertion `2 = 1 + 1` | NO | Uses α_YM, α_Poincaré values | None — the "+1" is not tied to any substrate operator | The `+1` is not a substrate quantity. Would require a **canonical substrate operation** that maps the Poincaré-class invariant to the YM-class invariant by an intrinsic shift of exactly 1. Not attempted. |
| **I9** | `α_RH · α_YM = 3` | `norm_num` (`(3/2) · 2 = 3`) | **E + F** | YES — chosen so `(3/2) · 2 = 3` | NO | Uses α_RH, α_YM values | The integer `3` could come from base-3 substrate (the "3" of `T_∞ = 3^∞`) | The "3" on the RHS is the *only* structural constant in the eight-law system that could plausibly come from the base-3 substrate. But **no theorem currently links `3 = base_of_substrate` to the product `α_RH · α_YM`.** |

### 4a. Summary of provenance codes

| Code | Laws carrying it |
|---|---|
| **A** — intrinsic PF theorem | **none** |
| **B** — conditional | none |
| **C** — rigidity of assigned | none (r128 provides the rigidity of the *tuple*, not of the *laws*) |
| **D** — definitional | L1, L2, L4 |
| **E** — trivial arithmetic | L3 (under `q=1/4`), I6, I7, I9 |
| **F** — target-encoded | L1, L2, L3, L4, L5 (on canonical), I6, I7, I9 |
| **G** — unsupported narrative | L5, and the docstring-only Galois narratives on L1, L2, L3, L4 |
| **H** — external classical | none (the Perelman anchor is a *separate* input to the anchored variant, not a member of `StructuralLaws`) |

**No law carries provenance code A.** The eight-law system is entirely (D ∪ E ∪ F ∪ G).

### 4b. Absence of mathlib Galois API

The four laws L1, L2, L3, L4 are presented in the docstrings as Galois-theoretic — minimal polynomials over `ℚ` and `ℚ(√5)`, trace and norm on `ℚ(√2)`, `ℚ(√(2π))`, and the coset `φ + ℚ`. The kernel proofs invoke:

- `Real.mul_self_sqrt` (mathlib)
- `Real.sqrt_pos` (mathlib)
- `nlinarith`, `linarith`, `positivity`, `ring` (tactics)

The mathlib namespaces **`Polynomial.minpoly`**, **`Algebra.trace`**, **`Algebra.norm`**, **`IntermediateField`**, **`NumberField`** are not invoked anywhere in `AlphaSkeletonUniqueness_r128.lean` or `CrossMillenniumSharedInvariants.lean`. The Galois narrative is prose only.

## 5. Independent generating set of the eight laws

Working over ℝ with `α_Poincaré, α_Hodge, α_P, α_YM, α_RH, α_NP, α_QG, α_NS, α_BSD` as free variables:

- **Purely-algebraic dependencies** (each is a solvable-for-one-variable relation):
  - I7 solves for `α_YM` given `α_Poincaré`.
  - I9 solves for `α_RH` given `α_YM`.
  - L2 solves for `α_P` given `α_YM` (with `α_P > 0`).
  - L1 solves for `α_Hodge` given `α_Poincaré` (with `α_Hodge > 0`).
  - L4 solves for `α_QG` given `α_YM` (with `α_QG > 0`).
  - L3 solves for `α_NP` given `α_Poincaré, α_RH, α_Hodge`.
  - L5 solves for `α_NS` given `α_RH`.
  - I6 solves for `α_BSD` given `α_NS, α_YM`.

The eight laws are algebraically **independent**: each pins a distinct α-variable that no other law fixes. **Dropping any one law removes rigidity for the corresponding α.**

- **Concrete dependency check on the 1-parameter free family** (r124 Gröbner-effective rank 8 in 9 unknowns): the sub-system {L1, L2, L3, L4, I6, I7, I9} has rank 7 and admits a **1-parameter family** in `α_BSD`. Adding L5 closes it. r124 identified this same free parameter independently.

**Minimum independent structural-law generating set has size 8 (all eight are required).**

The only compressions available are notational, not structural:
- Under `α_NP − α_Hodge = 1/4` (a consequence of L3 at the canonical point), L3 becomes "the offset q equals `1/4`." Adopting `q = 1/4` as a primitive replaces L3 with L3', but the informational content is identical.
- If any α-value acquires a *substrate derivation* (r128 shows this suffices for tuple uniqueness), the corresponding law becomes formally redundant *as an input* — but the seven remaining laws must still be assumed to obtain the other seven α-values.

## 6. Numerical-information content per law

For each law, "numerical information content" = the number of independent real values it fixes when the α-values on its RHS are treated as inputs. All eight are single-equation laws pinning one real, hence content = 1 each.

But a sharper accounting is: **how many rationals (or π-multiples) with denominator ≤ 4 must be inserted to state the law?**

| Law | Constants on RHS | Numerical insertions | Would be true if α's were re-scaled? |
|---|---|---|---|
| L1 | `0` (`x² − x − 1 = 0` after unfold) | 0 (given `α_Poincaré = 1`) | NO — depends on `α_Poincaré = 1` on the RHS |
| L2 | `0` (`x² = α_YM`) | 0 | NO if `α_YM ≠ 2` |
| L3 | integer 2, integer 1 | 2 numerical constants (`+1`, `×2`) | Requires exact `q = 1/4` |
| L4 | π | 1 (the factor π) | Requires exactly π on RHS |
| L5 | π | 1 (the factor π) | **Uniquely load-bearing — see §4** |
| I6 | none | 0 | NO if any α ≠ canonical |
| I7 | integer 1 | 1 | NO if `α_YM − α_Poincaré ≠ 1` |
| I9 | integer 3 | 1 (the integer 3) | NO |

Total numerical insertions across the eight laws: **≥ 6 explicit rational or π-multiple constants** (`+1` in I7, `×2, +1` in L3, `π` in L4 and L5, `3` in I9). Every one of these is **exactly the value that makes the canonical α-tuple satisfy the law.**

## 7. Table 2 — CANDIDATE GENERATORS

Each row lists a **candidate mechanism** that could conceivably become the substrate-derivation source for one or more structural laws, together with the α-seeds it might also derive.

| # | Candidate generator | Laws it could explain | α-seeds it could also explain | Current PF corpus support | Circularity risk | Smallest testable theorem |
|---|---|---|---|---|---|---|
| **H1** | H_3 icosahedral Coxeter group as intrinsic symmetry of a canonical base-3 substrate object | L1 (via minimal polynomial of φ = 2·cos(π/5)) | `α_Hodge = φ`, secondarily `α_NP = φ + 1/4` if the "1/4" is derived as 1/(top-exponent-gap) | `H3CoxeterOrigin.lean` proves the arithmetic identities (`cos(π/5) = φ/2`, exponents `{1,5,9}`, Coxeter number 10, `sin(π/10) = 1/(2φ)`). The **substrate → H_3** bridge is not proved. | LOW — mathlib supplies `Real.cos_pi_div_five` and `Polynomial.minpoly ℚ φ = X² − X − 1` is a genuine external computation | Prove `SymmetryGroup(base_3_period_2_fixed_points) ≃ CoxeterGroup H_3` (order-120 icosahedral acts on the 9-element base-3 period-2 set). Currently `basethree_period2_fixed_points.card = 9` is proved (r25); no automorphism-group theorem exists. |
| **H2** | Base-3 substrate cardinality invariant `3` | I9 (the RHS `3`), potentially I7 (the `+1` as `3 − α_YM = 1`) | `α_Poincaré = 1` as multiplicative identity of `T_∞`, `α_YM = 2` as `3 − 1` | The base-3 structure is intrinsic (`T_∞ = 3^∞` is proved; `τ_*(K_0(T_∞)) = ℤ[1/3]` in r123). No theorem currently connects the integer `3` in I9's RHS to base-3. | MODERATE — the number `3` appears on both sides but the CONNECTION `3_substrate → 3_invariant` requires an intrinsic pairing form on `K_0(T_∞)` | Prove `∃ canonical bilinear form B on K_0(T_∞): B(1, 2) = 3` (or the analogue for `α_RH · α_YM`), and identify `α_RH` with a canonical K-theory class under this form. |
| **H3** | `H_3` top exponent = 9 → offset `1/4` as `1/(top_exponent − 1) · 2 = 1/4` or similar arithmetic combinatorics of H_3 exponents | L3 (specifically the offset `q = 1/4`) | `α_NP − α_Hodge = 1/4` becomes intrinsic given H1 | The four convergent facets of the 9-count (r25) are arithmetic coincidences; no formalized "offset from exponent gap" theorem | HIGH — many arithmetic expressions in the H_3 exponents can equal `1/4`; would need a canonical selection rule | Prove a specific combinatorial identity: `1/(top_exponent H_3) + 1/(Coxeter number H_3) · something = 1/4` with a canonical, non-cherry-picked construction. |
| **H4** | Circle group `SO(2)` scaling / π as canonical continuum-limit factor for base-3 substrate | L4 (the factor `π` in `α_QG²`), L5 (the factor `π` in `α_NS`) | `α_QG = √(2π)`, `α_NS = 3π/2` | `SubstrateOscillator_r223` produces `π`-valued abscissae in specific oscillator settings. No canonical continuum-limit theorem is formalized. `π` is not derived as a substrate invariant. | HIGH — `π` appears in mathlib for many reasons; the RISK is choosing a coincidental derivation | Prove `∀ canonical measure μ on base_3_continuum: ∫ μ = π · (something intrinsic)`. Nothing of this form currently exists. |
| **H5** | Perelman theorem as external classical anchor + r128 forward cascade | (indirectly, given L1–L5, I6, I7, I9): none of the laws themselves; only the anchor | `α_Poincaré = 1` from Perelman 2003 | Anchor is *cited*; `α_Poincaré = 1` is `def`, not `theorem` (see `CrossMillenniumSharedInvariants.lean`) | LOW as an anchor; does not touch laws | Prove `α_Poincaré = 1` from a formalized Perelman argument. **This is Ricci-flow-scale work, currently completely unformalized.** Not tractable as "smallest testable." |
| **H6** | BSD-side anchor: `α_BSD = 3π/4` from literal L-function data (r128 §5) | (indirectly): none of the laws themselves; only the alternative anchor | `α_BSD = 3π/4` from a BSD-form derivation | The r128 §5 backward cascade exists (`alpha_skeleton_unique_from_BSD`). The BSD-derivation itself is not attempted. | LOW as an anchor; does not touch laws | Currently intractable at PF scale. |
| **H7** | Explicit r123 no-go extension: prove `∀ canonical PF invariant I: I ≠ π · (rational)` for the substrate | Would formally **refute** L4 and L5 as substrate-intrinsic; force them to remain external inputs | Would confirm: `α_NS, α_QG` are NOT substrate-derivable | r123 already excludes 7 of 9 α-values from `ℤ[1/3]`. Extending to explicit π-multiple no-go should be tractable (π is transcendental over ℚ, so `π · ℚ ∩ ℤ[1/3] = {0}`) | LOW — the no-go direction avoids all target-encoding | Prove `∀ x ∈ ℤ[1/3], x ≠ 3π/2` (elementary: LHS ⊂ ℚ, RHS ∉ ℚ by `irrational_pi`). This is a one-liner. |
| **H8** | Mathlib Galois API bridge for the currently-narrative L1–L4 | Would upgrade L1, L2, L4's provenance from **D + F** to **D + F + intrinsic-galois-witness** (still not A, but at least the docstring would be formal) | None of the α-values | Not currently attempted in the corpus | LOW — Galois witnesses without a substrate bridge don't derive α; they just formalize the *narrative* | Prove `Polynomial.minpoly ℚ ((1+√5)/2) = X² − X − 1` (mathlib supplies enough; may need a wrapper). Similarly for `√2`, `√(2π)`. |

## 8. Audit of the Perelman α = 1 normalization itself

**Statement in the corpus.** `α_Poincaré` is a `noncomputable def` equal to `(1 : ℝ)` in `PF/CrossMillenniumSharedInvariants.lean`. The Perelman anchor is invoked as the **narrative** justification for the value `1`. It is NOT a `theorem` in the corpus. The equation `s.aPoincare = 1` appears as an assumption (`anchor : s.aPoincare = 1`) in `SkeletonLaws`, not as a proved fact.

**Formal status.** External classical (Perelman 2003, three-manifold Poincaré via Ricci flow). Not formalized in mathlib. Not formalized in PF.

**Numerical content.** One numerical value (`1`).

**Alternatives.** The `α_Poincaré = 1` normalization is a **choice of unit**. Perelman's theorem states that any closed simply-connected 3-manifold is homeomorphic to `S³`; the corresponding "α" is a labeling convention. The value `1` (rather than any other positive real) is a normalization convention motivated by:

- Structural: the multiplicative identity of a C*-algebra is always `1`, so `α_Poincaré = 1 ↔ α_Poincaré = mult identity` is a specific identification, not a forcing.
- Numerological: the four convergent facets of the 9-count (r25) use `1` as the base of the counting.

**Consequence of the normalization choice.** All eight laws inherit their exact numerical content from this choice:
- I7 gives `α_YM = 2` because `α_Poincaré = 1`.
- I9 gives `α_RH = 3/2` because `α_YM = 2`.
- L1 gives `α_Hodge = φ` because `α_Poincaré = 1` (the minimal-polynomial constant term is `−α_Poincaré = −1`).
- L2 gives `α_P = √2` because `α_YM = 2`.
- L4 gives `α_QG = √(2π)` because `α_YM = 2`.
- L3 gives `α_NP = φ + 1/4` because `α_RH = 3/2` and `α_Hodge = φ`.
- L5 gives `α_NS = 3π/2` because `α_RH = 3/2`.
- I6 gives `α_BSD = 3π/4` because `α_YM = 2` and `α_NS = 3π/2`.

**Verdict.** The Perelman anchor is a **normalization** contributing one bit of information: the choice of unit `α_Poincaré = 1`. All other α-values are then forced by the eight laws. This is exactly the "one seed, eight laws, positivity → rigid" claim of r128.

**But the eight laws themselves are 6 numerical insertions.** So the total inserted information is:

- **1 anchor value** (`α_Poincaré = 1`)
- **6 numerical constants** in the laws (`+1` in I7; `×2, +1` in L3; `π` in L4; `π` in L5; `3` in I9)
- **8 structural equations** (choice of which quantities are related to which)
- **9 positivity assertions**

Total: on the order of **~15 real-valued insertions** to pin the 9 α-values. Not "one seed forces nine values" in the sense of substrate-intrinsic derivation. Rather: "one seed + eight *pre-chosen algebraic relations* + positivity forces the tuple."

## 9. Independence audit — what would break if we dropped each law?

If law X is dropped, the corresponding α-value becomes a free parameter (of the surviving algebraic system):

| Dropped law | Newly-free α | Effect on other α's |
|---|---|---|
| L1 dropped | `α_Hodge` free | `α_NP` becomes free (via L3) |
| L2 dropped | `α_P` free | isolated |
| L3 dropped | `α_NP` free | isolated |
| L4 dropped | `α_QG` free | isolated |
| L5 dropped | `α_NS` free | `α_BSD` becomes free (via I6). **This is exactly r124's identified 1-parameter Gröbner family in `α_BSD`.** |
| I6 dropped | `α_BSD` free | isolated (given L5 fixes `α_NS`) |
| I7 dropped | `α_YM` free | `α_P, α_RH, α_QG` all free |
| I9 dropped | `α_RH` free | `α_NS, α_NP` free (via L5, L3) |

**Most-cascading law: I7 (`α_YM = α_Poincaré + 1`).** Dropping I7 destroys rigidity of 4 α-values.
**Second most-cascading: I9 (`α_RH · α_YM = 3`).** Dropping I9 destroys rigidity of 3 α-values.
**Least-cascading: L2, L3, L4, I6.** Each is a single-α pinner.

**Critical narrative-gap law: L5.** Not the most cascading, but it is the only law whose *presence* was traced by r124's Gröbner analysis to close the free parameter. Removing L5 exhibits the 1-parameter freedom in `α_BSD` that r124 detected.

## 10. Recommended smallest non-circular theorem

Per DIRECTIVE Part XII, preference order is:
1. Closest to formal completion in the current corpus.
2. Fewest new definitions.
3. Fewest new mathlib API surfaces.
4. Zero project axioms; kernel-clean.
5. Result convertible to something reusable elsewhere in PF.

The candidate that maximizes all five criteria is:

### **Recommendation: L5 K-theoretic no-go.**

```lean
theorem l5_not_derivable_from_ktheoretic_ratio :
    ∀ (a b : ℝ), MemZ13 a → MemZ13 b → a ≠ 0 → b / a ≠ Real.pi
```

**Meaning.** No ratio of two nonzero elements of the substrate K-theory range `ℤ[1/3] = τ_*(K_0(T_∞))` equals π. Consequently, if the π-scaling law L5 is ever to be given a substrate origin, that origin cannot be `α_NS / α_RH` (interpreting numerator and denominator as substrate K-theory values). The K-theoretic route to L5 is formally closed.

**Proof route** (READ-ONLY — not implementing):
1. `MemZ13 x → x ∈ Set.range ((·) : ℚ → ℝ)` — this is r123's `memZ13_isRat` (already in the corpus).
2. Nonzero ratio of rationals is rational (mathlib: division field structure).
3. Rational ≠ π via mathlib's `Irrational` API: `Nat.Prime.irrational_sqrt` template does not apply; the relevant theorem is `Real.pi_irrational` (mathlib name `irrational_pi` in some versions; `Real.irrational_pi` in others — verify at implementation time).

**Why this recommendation:**

- **Closest to formal completion.** The K-theory embedding `ℤ[1/3] ⊂ ℚ` is already proved (r123). `Real.pi` is irrational in mathlib (`irrational_pi`). The proof is essentially a three-line contradiction.
- **Fewest new definitions.** Zero new definitions. `MemZ13`, `Real.pi`, `Real.pi_irrational` all exist.
- **Fewest new mathlib API surfaces.** Only `Irrational` and rational-of-K-theory (already available).
- **Zero project axioms.** Trivially kernel-clean.
- **Reusability.** Converts L5's provenance from "unsupported narrative (code G)" to "provably-outside-K-theory (code A no-go, structurally analogous to r123's α-exclusion)." This *is* the companion no-go the intrinsic-origin audit §12 recommended, restricted to the specific structural law that r124's Gröbner analysis flagged as the free-parameter closer.

**Precise scope statement.** The theorem does NOT claim L5 is unprovable in any substrate. It states: **no route to L5 via K-theoretic ratios of α-values inside `ℤ[1/3]` can exist.** It converts one "unsupported narrative gap" into a formal exclusion result, which is scientifically valuable and does not overreach.

**What this theorem is NOT.**
- NOT a proof that L5 is false (L5 holds for the canonical α-tuple).
- NOT a proof that L5 has no substrate derivation whatsoever (a substrate producing π-multiples outside K-theory is not ruled out).
- NOT a proof that the substrate has to be extended (that would require the *positive* companion theorem).

## 11. Explicit language required by the DIRECTIVE

Per the anti-scaffolding requirement: the correct honest status is

> **"the solution space of the r128 `StructuralLaws` is one-anchor rigid under positivity"**

NOT

> ~~"the effective dimension of the intrinsic α-skeleton = 1"~~.

The eight laws are inputs. Their content is not intrinsically PF-derived. The r128 rigidity is a rigidity of the **algebraic system {8 laws + positivity}**, not of any substrate-intrinsic object. The one-parameter reduction from 9 α-values to 1 seed applies **conditional on accepting the eight laws as inputs**.

## 12. What changed from the intrinsic-origin audit

The intrinsic-origin audit examined **α-generation mechanisms** and found zero mechanisms in provenance class A. This audit examined the **eight structural laws themselves** and found the same: **zero laws in provenance class A**.

The two audits together yield a symmetric picture:

- **α-values** are inserted as `def`.
- **Laws** are inserted as algebraic assertions chosen precisely to be satisfied by the pre-declared α-values.
- The r128 rigidity theorem is genuine but is a rigidity of the *composite input system*, not of any intrinsic PF object.

The **new fact surfaced by this audit** is L5's status as the load-bearing narrative gap. L5 has no docstring-Galois narrative (unlike L1, L2, L3, L4) and no corpus-invariant status (unlike I6, I7, I9). It is the sole naked assertion `α_NS = α_RH · π` that closes r124's Gröbner-identified free parameter. This is the specific location where the α-web's algebraic rigidity depends on a completely un-motivated equation.

The **best structural target** — smaller than the α-derivation targets of the prior audit — is therefore the **L5 K-theoretic no-go**, which converts this one narrative gap into a formal exclusion in a single small theorem using only existing corpus infrastructure.

---

## Summary

| Aspect | Finding |
|---|---|
| Minimum independent structural-law generating set | **8 laws** (all are required; each pins a distinct α) |
| Laws with provenance class A (intrinsic PF theorem) | **0** |
| Laws with provenance class D or E (definitional / trivial arithmetic) | **7** (all except L5) |
| Laws with provenance class F (target-encoded) | **8** (all) |
| Laws with provenance class G (unsupported narrative) | **L5** primarily; L1–L4 carry G-tinted docstring narratives |
| Laws formally using mathlib Galois API (`Polynomial.minpoly`, `Algebra.trace`, `Algebra.norm`) | **0** |
| Most-cascading law under drop | **I7** (destroys 4 α's) |
| Load-bearing narrative-gap law | **L5** (r124's free-parameter closer) |
| Perelman anchor formal status | External classical, cited via `def α_Poincaré := 1`, not a theorem |
| Total numerical constants inserted across the eight laws | **≥ 6** rationals or π-multiples |

**Recommended smallest non-circular theorem (READ-ONLY recommendation; NOT implementing):**

```
theorem l5_not_derivable_from_ktheoretic_ratio :
    ∀ (a b : ℝ), MemZ13 a → MemZ13 b → a ≠ 0 → b / a ≠ Real.pi
```

**Status statement (correct wording):** the solution space of the r128 `StructuralLaws` is one-anchor rigid under positivity, conditional on accepting the eight laws as inputs; none of the eight laws has an intrinsic PF-substrate derivation, and L5 is the unique law whose narrative motivation has no formal counterpart anywhere in the corpus.

**Not implementing the recommended theorem without your authorization.** Per DIRECTIVE: STOP after producing this audit.

---

**End of audit.**

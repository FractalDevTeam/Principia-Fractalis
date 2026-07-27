# Attempting to Derive `α_NP = φ + 1/4` — Results

**Date:** 2026-07-26
**Predecessor:** `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md` (the circularity audit)
**Formalization:** `PF_Lean4_Code/PF/AlphaNPDerivationAttempt_r122.lean`
— builds clean, zero `sorry`, zero project axioms, kernel-only
`[propext, Classical.choice, Quot.sound]`.
**Status of `α_NP`:** bucket 2 (asserted, difficulty unknown). This is the
first direct attempt at the derivation.

---

## 0. BOTTOM LINE

> **Nothing derives `φ + 1/4` from operator theory, spectral geometry, or the
> ternary substrate.** No such route exists in the corpus and none was found.
>
> **Two real results were obtained.**
>
> **(A) POSITIVE — the `+1/4` is not a free parameter; it is a Galois trace.**
> Inside the golden sector, the single cross-sector postulate
> `Tr_{ℚ(√5)/ℚ}(α_NP) = α_RH` forces `α_NP = φ + 1/4` exactly, and forces the
> quadratic `16α² − 24α − 11 = 0` as a consequence. The `1/4` becomes
> `(α_RH − α_Poincaré)/[ℚ(√5):ℚ] = (3/2 − 1)/2`, built entirely from constants
> the framework fixes in *other* sectors. **This is non-circular** — unlike
> `α_NP − α_Hodge = 1/4`, whose only proof is `unfold; ring` on the value.
> It is a *reduction*, not an elimination: one free rational is traded for one
> postulate of the same information content.
>
> **(B) NEGATIVE / IMPOSSIBILITY — the stated postulates do not determine
> `α_NP`, and this is now machine-checked.** With the definitional clause
> removed, the framework's entire α-skeleton plus positivity plus the
> `AlphaRealizationNoGo` distinctness clause plus the universal coupling
> admits a model with `α_NP = r` **for every real `r > 0`, `r ≠ √2`**
> (`alphaNP_unconstrained`). The pin is therefore an **axiom or an empirical
> input**, definitively — not a consequence of anything else the framework
> asserts.
>
> **Third result, smaller but sharp:** the π/10 ↔ H₃ thread — the most
> promising lead going in — **produces `φ` exactly and uniquely, and provably
> excludes `φ + 1/4`.** The framework can motivate the golden ratio. It
> cannot, by that route, motivate the offset.

---

## 1. TASK 1 — WHERE COULD A RATIONAL `1/4` COME FROM?

Four candidates were tested. Verdicts first, then the work.

| Candidate | Gives exactly 1/4? | Verdict |
|---|---|---|
| (a) H₃ rank/dimension/exponent-gap | yes (4 = gap) | **fit** — and a cheap one, see §1.1 |
| (b) base-3 substrate | yes (`1/(b+1)`, `b=3`) | **fit** — and it *collides* with (a), which weakens both |
| (c) Maslov / semiclassical index | no | **unsupported** — no WKB content exists in the corpus |
| (d) `α_NP − α_Hodge = 1/4` | yes, by definition | **circular** — this IS the assertion |

### 1.1 (a) H₃ combinatorics — the match is cheap, and that is measurable

`H3CoxeterOrigin.lean:244-248` matches `1/4` to `1/(H₃ exponent gap)`. The
audit already called this numerology. This attempt **quantifies how cheap it
is.**

Take the pool of integers H₃ actually supplies —
`{1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 15, 20, 30, 60, 120}` (rank, exponents
{1,5,9}, gap 4, degrees {2,6,10}, Coxeter number 10, `h+1`, reflections 15,
roots 30, `|W| = 120`, and small products) — and form all ratios
`a/b`, `a/b²`, `a²/b`. That yields **309 distinct positive rationals**, of
which **11 lie within ±0.05 of 1/4**:

```
1/5, 5/24, 2/9, 6/25, 20/81, 30/121, 1/4, 4/15, 3/11, 5/18, 3/10
```

So the "H₃ predicts 1/4" observation had a ~1-in-1 chance of succeeding
against a 3-decimal target from this pool. **It carries essentially zero
evidential weight.**

There is also a hard structural obstruction (§1.5, and Lean
`alphaNP_not_algebraic_integer`): H₃ cannot produce a `1/4` *integrally* at
all.

### 1.2 (b) The base-3 substrate

`1/4` is genuinely natural in base 3, in two independent ways:

* `1/4 = 0.020202…₃ = Σ_{k≥1} 2·3^{−2k}`;
* `1/4 = 1/(b+1)` with `b = 3` — i.e. `Σ_{n≥1} (−1)^{n+1} b^{−n}`, the
  alternating geometric constant of the substrate base.

Both are exact. **But this is the problem, not the solution.** The base-3
route and the H₃ route arrive at the *same* denominator 4 by unrelated
mechanisms (`b + 1 = 4` vs `exponent gap = 4`), and a third route does too:
the classical identity `∏_{k=1}^{m} cos(kπ/(2m+1)) = 2^{−m}` gives
`cos(π/5)·cos(2π/5) = 1/4` for the pentagon (verified to 40 digits).

Three unrelated "derivations" of the same number is the signature of an
over-determined *target*, not a converging *mechanism*. Any of the three
could be cited; none predicts that the result should be **added** to `φ`
rather than multiplied, subtracted, or exponentiated.

**Labelled: fit.**

### 1.3 (c) Maslov / semiclassical index shift — NOT SUPPORTED

Berry–Keating-type spectral asymptotics do carry `1/8` and `1/4` corrections,
and this was the most physically respectable candidate. It fails on contact
with the corpus:

* Grepping the entire repository for `Maslov` returns **zero hits**.
* The only WKB content is `PF/P_NP_Axiom_Elimination.lean:28-56` and
  `PF/P_NP_Complete_Proof.lean:94`, which *assert* that
  `λ₀ = π/(10α)` comes "from the WKB quantization condition". There is no WKB
  computation anywhere — `fractal_resonance α := pi_10 / α` is a definition,
  and `resonance_determines_ground_state` proves only that this definition is
  positive.
* The framework's `H_NP` is an **integral operator with a fractal-metric
  kernel on `L²(K_P, μ_P)`**, not a 1-D Schrödinger operator. Maslov indices
  are a property of turning points of classical trajectories; there is no
  classical flow, no turning point, and no phase-space to count them in.

**A Maslov `1/4` cannot be produced from the framework's stated Hamiltonian
normalization, because that normalization is a definition, not a
quantization condition.** Labelled: unsupported.

### 1.4 (d) `α_NP − α_Hodge = 1/4` with `α_Hodge = φ` — which is the unknown?

`α_Hodge = φ` **is** independently motivated, and better than the audit gives
it credit for: `φ = 2cos(π/5)` is the off-diagonal entry of the H₃ Cartan
matrix (bond label 5). That is a *primitive* appearance — no choice of
operator, no dynamics, just the Coxeter diagram.

A stronger observation, apparently not recorded in the corpus (nearest is
`CrossMillenniumMoreInvariants.lean:262`, which has only the `φ` case):

> **The Cartan bond-value ladder `2cos(π/m)` for `m = 3, 4, 5, ∞` yields
> exactly `{1, √2, φ, 2}` = `{α_Poincaré, α_P, α_Hodge, α_YM}`.**

Four of the nine α-values from one formula with one integer parameter taking
only its allowed Coxeter values. That is a genuinely uniform structure and is
much stronger than the per-value ad hoc rules in `H3CoxeterOrigin.lean`.
(Honest caveats: it was found by looking at the answers; `m = 6` gives `√3`,
which is *not* an α, so the ladder has a hole; and `α_RH = 3/2` is not on it
— `2cos(π/m) = 3/2` needs `m ≈ 4.347`.)

**Consequence for `α_NP`:** `α_NP` is the *only* α with a plausible bond-value
neighbour that it misses. `2cos(π/9) = 1.87939…` versus
`φ + 1/4 = 1.86803…` — close, but not equal, and the H₃ exponent 9 makes the
near-miss tempting. It is a near-miss. Verified to 12 digits.

So: **`α_Hodge = φ` is the well-motivated half, and the `1/4` is the real
unknown.** Candidate (d) is the framework's own circle and derives nothing.

### 1.5 A hard obstruction: `φ + 1/4` is not an algebraic integer

Machine-checked (`alphaNP_not_algebraic_integer`):

> **There are no integers `a, b` with `a + b·φ = φ + 1/4`.** I.e.
> `α_NP ∉ ℤ[φ]`.

`ℤ[φ]` is the ring of integers of `ℚ(√5)`, and it contains **every** quantity
the H₃ Coxeter data produces: Cartan entries (`2cos(π/5) = φ`, `1`, `2`),
eigenvalues of the Coxeter element in the maximal real subfield of `ℚ(ζ₁₀)`,
character values of `H₃ ≅ ℤ/2 × A₅`, root coordinates. (`2` is inert in
`ℚ(√5)`, so `v₂(α_NP) = −2` exactly: the denominator is genuinely 4 and
cannot be cleared.)

**Therefore no ℤ-polynomial combination of H₃ invariants equals `α_NP`.** Any
H₃-based derivation must at some point *divide* by 4, and the Coxeter data
supplies no canonical division. This is the precise reason the exponent-gap
match is a fit: it is an ad hoc division dressed as a structure.

### 1.6 Cross-field remark

`α_P = √2 ∈ ℚ(√2)` and `α_NP = φ + 1/4 ∈ ℚ(√5)` generate **different**
quadratic fields. Any single mechanism producing both must generate
`ℚ(√2, √5)`, degree 4 over ℚ with Galois group `(ℤ/2)²` and conductor 40.
No object in the corpus has that symmetry. This is a real constraint on any
future unified derivation and does not appear to have been stated.

---

## 2. TASK 2 — THE π/10 LINK, WORKED EXPLICITLY

**This was the most promising thread. It resolves cleanly, and negatively for
the `+1/4`.**

### 2.1 First, the coupling itself is empty

Framework claim: `λ₀(α)·α = π/10`, "universal". Formalized and disposed of
(`coupling_determines_no_alpha`):

> For **every** `α > 0` there exists `λ₀` with `λ₀·α = π/10`, namely
> `λ₀ := π/(10α)`.

The coupling is a **change of variables on `(0,∞)`**, a bijection
`α ↦ π/(10α)`. It is satisfied by every positive real and therefore
constrains none. Every corpus argument of the shape "the universal coupling
pins α" is void — including, retroactively, the whole of Circle 3 in the
2026-07-25 audit (the `π/(10(φ+1/4))` round-trip): that loop was not merely
circular, it was circular *through a tautology*.

### 2.2 The only non-trivial way to combine π/10 with H₃

The two ingredients are:

* the coupling `λ₀·α = π/10` (framework);
* `sin(π/10) = 1/(2φ)` (classical, machine-checked at
  `H3CoxeterOrigin.sin_pi_div_ten_eq_inv_two_phi`).

The single natural closure — make `α` the fixed point of its own coupling
angle under the icosahedral sine —

```
    α = 1 / ( 2 · sin(λ₀(α) · α) )        [IcosahedralSelfConsistency]
```

has, since `λ₀·α ≡ π/10`, the unique solution

```
    α = 1 / (2 · sin(π/10)) = φ.
```

**Formalized:** `icosahedral_self_consistency_forces_goldenRatio` — the
solution is `φ`, exactly and uniquely. And
`alphaNP_fails_icosahedral_self_consistency` — `φ + 1/4` provably fails it.

The failure is quantified exactly
(`icosahedral_residual_at_alphaNP`):

```
    2·(φ + 1/4)·sin(π/10) = 1 + 1/(4φ)  =  1 + (φ − 1)/4  ≈  1.1545
```

### 2.3 Verdict on Task 2 — a real partial result

> **The π/10 coupling combined with `sin(π/10) = 1/(2φ)` yields `φ`, and only
> `φ`. It is silent about the `+1/4`, and the natural self-consistency
> condition actively excludes `φ + 1/4`.**

This is exactly the outcome the task anticipated as "real and important", and
it should be stated in the manuscript in place of any suggestion that the
`π/10` ↔ H₃ coincidence supports `α_NP`. **It supports `α_Hodge`. It refutes
its own extension to `α_NP`.**

---

## 3. TASK 3 — THE QUADRATIC `16x² − 24x − 11 = 0`

### 3.1 The polynomial has no content beyond a trace and a discriminant

Machine-checked (`NP_quadratic_iff_trace_disc`,
`NP_quadratic_coefficients_from_trace_disc`):

```
    16x² − 24x − 11 = 0     ⟺     (2x − 3/2)² = 5
                            ⟺     (2x − α_RH)² = disc ℚ(√5)
```

Generally, for trace `T` and discriminant `D`, `(2x − T)² = D` clears to

```
    16x² − 16T·x + (4T² − 4D) = 0.
```

Substituting `T = α_RH = 3/2`, `D = 5`:

* `16·T = 24` ✔ (`NP_quadratic_integers_explained`)
* `4D − 4T² = 20 − 9 = 11` ✔
* discriminant `24² + 4·16·11 = 1280 = 16²·5` ✔
  (`NP_quadratic_discriminant`)

**So the "1280 = 2⁸·5" observation resolves completely: the `5` is the golden
discriminant, and the `2⁸` is `(leading coefficient)²`, pure bookkeeping from
clearing the `/4`.** The integers 16, 24, 11 are *not* independent structure.
They are `(4, 4T, 4T² − 4D)` scaled by 4. There is nothing in them beyond the
pair `(α_RH, 5)`.

Corollary: any argument of the form "the self-adjointness quadratic
`16α² − 24α − 11 = 0` forces `φ + 1/4`" is exactly the statement "trace 3/2
and discriminant 5 force `φ + 1/4`" — true, and equivalent to the value, as
`AlphaCanonical.lean:108-155` already proves.

### 3.2 Did the coefficients come from a postulate? Yes — but only via §4

`trace_law_forces_NP_quadratic` derives `16α² − 24α − 11 = 0` from the trace
postulate, not from the value. That is the correct logical direction
(criterion → quadratic, per the audit's requirement (3)), but the criterion is
§4's trace law, not an operator-theoretic condition. **No self-adjointness
condition producing this polynomial was found or constructed.**

### 3.3 Failed structural readings, recorded so they are not re-tried

* `24/16 = 3/2 = 15/10` (H₃ exponent-sum over Coxeter number) — true, but this
  *is* `T = α_RH`; nothing new.
* `11 = h(H₃) + 1` and `16 = gap²` — arithmetically true, so the quadratic can
  be written `α² − (Σe/h)·α − (h+1)/g² = 0`. **Rejected as numerology**: the
  `11` is not free (it is `4D − 4T²`), so matching it to `h + 1` is matching a
  *derived* quantity to a coincidence. The apparent "check" that the
  discriminant comes out to exactly 5 (`9/4 + 11/4 = 5`) is not a check at all
  — it is forced.
* Base 3: `T = 3/2 = Σ_{n≥0} 3^{−n}`, the total geometric mass of the ternary
  substrate. Suggestive, unproved, and it is a statement about `α_RH`, not
  `α_NP`.

---

## 4. THE POSITIVE RESULT — THE GOLDEN-SECTOR TRACE LAW

**Statement** (`alphaNP_from_golden_sector_trace_law`, machine-checked):

Let `σ` be the non-trivial automorphism of `ℚ(√5)`. Postulate:

* **(S1) Unit golden modulation.** `α_NP − α_Hodge ∈ ℚ`, with
  `α_Hodge = φ`. Equivalently `α_NP − σ(α_NP) = φ − σ(φ) = √5` — `α_NP`
  inherits the golden spread unchanged (`sectorSpread_eq`).
* **(S2) Cross-sector trace law.** `Tr_{ℚ(√5)/ℚ}(α_NP) = α_RH`.

Then, since `Tr(φ + q) = 1 + 2q` (`sectorTrace_eq`) and `Tr(φ) = 1 =
α_Poincaré`:

```
    α_NP  =  φ  +  (α_RH − α_Poincaré) / [ℚ(√5):ℚ]
          =  φ  +  (3/2 − 1)/2
          =  φ  +  1/4                                    ∎
```

and the quadratic `16α² − 24α − 11 = 0` follows
(`trace_law_forces_NP_quadratic`).

### 4.1 Why this is better than everything currently in the corpus

| | corpus invariant I10 | this |
|---|---|---|
| statement | `α_NP − α_Hodge = 1/4` | `Tr(α_NP) = α_RH` |
| proof of the hypothesis | `unfold α_NP α_Hodge; ring` | not needed — it is exogenous |
| mentions the answer | **yes** (`1/4` is literally in it) | **no** |
| circular | **yes** | **no** — `α_RH := 3/2` is defined without reference to `α_NP` |
| NP-specific free parameters | 1 (the rational `1/4`) | **0** |
| falsifiable | no | in principle: any independent pin on `α_RH` tests it |

The `1/4` is recovered as **half the framework's own critical-line offset**
`α_RH − α_Poincaré = 1/2`, with the `2` being the field degree
`[ℚ(√5):ℚ]` — a structural constant, not a fitted one. Equivalently, the
cleanest single identity is

```
    2·α_NP − α_RH = √5.
```

Every ingredient is already fixed elsewhere in the framework.

### 4.2 Ruthless assessment — this is a reduction, not a derivation

Be clear about what it is not:

1. **Information content is unchanged.** (S1) + (S2) are exactly two real
   conditions on the two ℚ-degrees of freedom of an element of `ℚ(√5)`.
   `1/4` in, `3/2` in — one real number either way. **No over-determination,
   hence no independent confirmation.** I looked for a third relation and
   found none (see 4.4).
2. **(S2) is itself unmotivated.** Why should the NP α-axis have Galois trace
   equal to the RH α-axis? Nothing derives this. It is a new postulate.
3. **It is still not operator theory.** It says nothing about `H_NP`,
   self-adjointness, trace class, or spectra. It fails audit requirements (1),
   (2) and (6) of `ALPHA_NP_DERIVABILITY_2026-07-25.md` §6.

What it *does* change: the free parameter is moved out of the NP sector
entirely, and into a cross-sector algebraic law that has the shape of
something a mechanism could produce. Post-hoc numerology on the digit `4` is
replaced by a Galois-theoretic statement. **The corpus should adopt this
formulation and drop I10** — it is strictly more honest and strictly more
informative at identical cost.

### 4.3 Partial pattern support for (S2)

The corpus already computes the traces (`CrossQuadraticFieldBridge.lean`
§7) without noticing the pattern:

| α | field | trace | matches | norm | matches |
|---|---|---|---|---|---|
| `α_Hodge = φ` | ℚ(√5) | **1** | `α_Poincaré` | **−1** | `−α_Poincaré` |
| `α_P = √2` | ℚ(√2) | **0** | — | **−2** | `−α_YM` |
| `α_NP = φ+1/4` | ℚ(√5) | **3/2** | `α_RH` | −11/16 | **nothing** |

Two of three traces land on the rational α-spine `{1, 3/2, 2}`. **But be
honest: `Tr(φ) = 1` is automatic (it is forced by `φ² = φ + 1`), so it is not
evidence.** The pattern therefore has exactly one non-trivial instance —
the one being fitted.

Note also the **norm law fails**: `N(α_Hodge) = −α_Poincaré` and
`N(α_P) = −α_YM` both land on the spine, but `N(α_NP) = −11/16` does not.
The choice of *trace* over *norm* as the operative law is therefore itself a
selection made after seeing the answer. Recorded as a weakness.

### 4.4 Search for over-determination — negative

Tested to 30 digits: `α_NP² − α_NP = 1.62152…` (not `φ = 1.61803…`);
`α_NP` is not `2cos(π/m)` for any integer `m` (nearest `m = 9` gives
`1.87939…`); `N(α_NP)` is not on the α-spine. **No third independently
motivated relation on `α_NP` was found.** The value is exactly determined by
(S1)+(S2) and no more.

---

## 5. TASK 4 — THE IMPOSSIBILITY DIRECTION

This is the most defensible deliverable, and it is now machine-checked.

### 5.1 The structural fact

Of the eleven clauses in
`CrossMillenniumSharedInvariants.cross_millennium_shared_invariants_capstone`,
**exactly one — clause (10), `α_NP − α_Hodge = 1/4` — mentions `α_NP` at
all**, and it is definitionally equivalent to the value
(`AlphaCanonical.lean:108-155`). The remaining ten are silent about `α_NP`.

The only other stated postulates mentioning `α_NP` are:

* positivity (`PolylogEigenvalueConjecture`);
* distinctness `α_NP ≠ α_P` — **the entire content** of
  `AlphaRealizationNoGo` (audit §3);
* the universal coupling `λ₀·α_NP = π/10` — **vacuous**, by §2.1 above.

### 5.2 The theorem

`alphaNP_unconstrained` (Lean, axiom-free):

> Let `AlphaSkeletonWithoutNPClause` be the framework's α-skeleton with
> clause (10) removed and every other stated constraint retained
> (ten invariants + positivity + `α_NP ≠ α_P` + the coupling).
> **For every real `r > 0` with `r ≠ √2` there is a model with `α_NP = r`,**
> all other nine α-values at their canonical framework values.

Corollary `alphaNP_not_determined`: two explicit models with different
`α_NP` (`1` and `φ + 1/4`).

### 5.3 What this settles

> **The framework's stated postulates do not determine `α_NP`.** The value is
> logically independent of everything the framework asserts except the
> assertion itself. `α_NP = φ + 1/4` must therefore be **an axiom or an
> empirical input.** There is no third option available from the current
> postulate set.

This is a clean impossibility result of the kind the task requested, and it
converts an open question into a closed one: *no amount of further work on
the existing postulates can produce the value.* Any derivation requires a
**new** postulate — either §4's trace law, or genuine operator theory not
present in the corpus.

### 5.4 Reinforcing the corpus's own negative result

`bare_route_structural_finding` shows the bare weighted-`G_n` reality
condition admits only `sin(πα) = 0` or `cos(πα) = −1/2`. This attempt kills
the first branch outright at `α_NP` (`sin_pi_alphaNP_ne_zero`, via
irrationality of `φ`), leaving `bare_route_at_alphaNP_forces_cos_branch`:

> If `Im β = 0` held at `α_NP`, then necessarily `cos(π·α_NP) = −1/2` —
> which forces `α_NP ∈ 2/3 + 2ℤ` or `4/3 + 2ℤ`, i.e. rational.

So the bare-GF route is not merely "does not close"; **at `α_NP` it is
inconsistent, and the surviving branch is inconsistent with irrationality.**
The corpus's most honest artifact gets sharper.

---

## 6. WHAT WAS *NOT* FOUND — RECORDED SO IT IS NOT RE-TRIED

* No self-adjointness, trace-class, or spectral criterion producing
  `16α² − 24α − 11 = 0`. The fractal-kernel route
  (`α^n` inside the cosine) remains `Prop := True` with three absent mathlib
  prerequisites; no partial computation of it exists, and none was attempted
  here (it is genuine novel analysis, not formalization labour).
* No Maslov/index origin — the corpus has no semiclassical structure to carry
  one (§1.3).
* No H₃-integral construction — provably impossible (§1.5).
* No third relation over-determining `α_NP` (§4.4).
* No degree-4 object with `Gal(ℚ(√2,√5)/ℚ) = (ℤ/2)²` symmetry that could
  produce `α_P` and `α_NP` from one mechanism (§1.6).

---

## 7. RECOMMENDED ACTIONS

Priority order, all cheap:

1. **Replace invariant I10 with the trace law.** State
   `Tr_{ℚ(√5)/ℚ}(α_NP) = α_RH` as the NP-sector postulate, cite
   `alphaNP_from_golden_sector_trace_law`, and delete
   `α_NP_sub_Hodge_eq_quarter` from the "rigidity" chain. Same content, zero
   circularity, and the `1/4` stops looking arbitrary.
2. **Withdraw all "the coupling pins α" language.** `coupling_determines_no_alpha`
   shows the coupling is a bijection. This affects
   `p_neq_np_spectral.tex:589/625`, the `ALPHA_UNIQUENESS_CERTIFICATION.md`
   extraction, and Circle 3 generally.
3. **Restate the H₃ result correctly:** "the π/10 ↔ icosahedral thread
   determines `α_Hodge = φ` uniquely and excludes `α_NP = φ + 1/4`"
   (§2). Present this as a *result*, because it is one.
4. **Publish the impossibility theorem** (§5). "The α_NP pin is provably
   independent of our stated postulates" is a stronger and more credible
   contribution than any forcing claim, and it is 100 lines of Lean.
5. **Delete the exponent-gap match** from `H3CoxeterOrigin.lean:244-248`, or
   annotate it with §1.1's cheapness count and §1.5's integrality
   obstruction.
6. **Add the Cartan bond-value ladder** `2cos(π/m)`, `m = 3,4,5,∞` →
   `{α_Poincaré, α_P, α_Hodge, α_YM}` (§1.4), with its hole at `m = 6`
   disclosed. It is the best genuine structure found in this pass.

---

## 8. THE MOST PROMISING REMAINING THREAD

**Derive the trace law.**

The question "why is `α_NP = φ + 1/4`?" is now exactly the question

> **why does the NP α-axis have Galois trace equal to the RH α-axis?**

That is a substantially better question than the one we started with. It is
cross-sector, it is algebraic, it is stated in terms of two objects that both
have independent (if heuristic) motivation, and it has a natural
operator-theoretic reading that does not yet exist but *could*: if the NP
operator has a two-dimensional invariant block whose two branch-eigenvalues
are the Galois conjugates `α_NP` and `σ(α_NP)`, then their sum is the trace
of that block, and the claim becomes

> **`tr(H_NP |_{2-dim golden block}) = α_RH`.**

`IBMPeaksGaloisPair.lean` already exhibits the 2×2 Hermitian realization
`H = m·I + d·σₓ` with eigenvalues `{α_RH, α_NP}` — but built *from* the
values. Building it *from the substrate* and computing its trace is the
concrete next target. It is real mathematics, it is bounded, and unlike the
fractal-kernel route it does not require three missing mathlib theories.

Second thread, smaller: find any **third** independently motivated relation
satisfied by `α_NP`. Over-determination is the only thing that would upgrade
§4 from a reduction to evidence.

---

## 9. SUMMARY TABLE

| Question | Answer | Where |
|---|---|---|
| Did anything derive `φ + 1/4` from operator theory? | **No** | §6 |
| Does the universal coupling constrain α at all? | **No — it is a bijection** | §2.1, Lean |
| Does π/10 + H₃ give `φ`? | **Yes, exactly and uniquely** | §2.2, Lean |
| Does π/10 + H₃ give `φ + 1/4`? | **No — provably excluded** | §2.2, Lean |
| Does `16x²−24x−11` carry independent structure? | **No — it is `(2x−α_RH)² = 5`** | §3.1, Lean |
| Where does `1/4` come from, structurally? | `(α_RH − α_Poincaré)/[ℚ(√5):ℚ]`, given the trace law | §4, Lean |
| Is that a derivation? | **No — a non-circular reduction, same information content** | §4.2 |
| Can H₃ produce `1/4` integrally? | **No — `α_NP ∉ ℤ[φ]`** | §1.5, Lean |
| Is the H₃ exponent-gap match evidence? | **No — 11 of 309 H₃-rationals land within ±0.05** | §1.1 |
| Is there a Maslov origin? | **No — no semiclassical structure exists** | §1.3 |
| Do the stated postulates determine `α_NP`? | **NO — every `r > 0`, `r ≠ √2`, extends to a model** | §5, Lean |
| So what is the pin? | **An axiom or an empirical input. Definitively.** | §5.3 |

---

*Attempt performed 2026-07-26. All numerics verified to ≥30 digits with
mpmath. All Lean claims build under
`lake build PF.AlphaNPDerivationAttempt_r122`, zero `sorry`, zero project
axioms, kernel-only `[propext, Classical.choice, Quot.sound]`.
No git commits made.*

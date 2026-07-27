# What the Proven Substrate Forces — and What It Provably Cannot

**Date:** 2026-07-26
**Scope:** read-only audit of the corpus + one new Lean file
(`PF_Lean4_Code/PF/AlphaFromSubstrateKTheory_r123.lean`, builds clean, kernel-only,
zero project axioms, zero sorries). No git commits. No existing file edited.
**Question:** given that `T∞` is now *provably* the Glimm `3^∞` UHF algebra
(r112/r113), what do the nine α-values have to be?

All paths are relative to `/home/xluxx/Principia-Fractalis`. Lean paths are
relative to `PF_Lean4_Code/`.

---

## 0. HEADLINE

> **The proven substrate does not fail to determine the α-values by accident.
> It cannot determine them, and this is now a theorem.**
>
> `M_{3^∞}` is a *purely 3-adic* object: every number its complete classifying
> invariant produces lies in `ℤ[1/3] ⊂ ℚ`. The framework's α-table is built
> almost entirely from the two primes the substrate provably cannot see —
> **2-adic** (`1/2`, `1/4`, `3/2`, `3π/4`) and **5-adic** (`φ`, `φ+1/4 ∈ ℚ(√5)`,
> `π/10 = π/(2·5)`, `h(H₃) = 10 = 2·5`). Exactly **two** of the nine α-values
> lie in `ℤ[1/3]`, and they are the two integers.
>
> The escape hatch — "α is a spectral value, not a trace value" — is closed from
> the other side: **every** real number, and every finite list of reals, is the
> spectrum of a self-adjoint element of `M_9 = M_{3²} ⊆ T∞`. So the spectral
> reading imposes no constraint whatsoever.
>
> **Dichotomy.** For each α-value, the substrate either *excludes* it
> (K-theoretic reading) or is *silent* about it (spectral reading). There is no
> reading on which it selects one.
>
> **And the sharpest single finding:** the corpus's *only* substrate-intrinsic
> definition of the α's — Conjecture 8.X.2 / `OPEN_PROBLEMS.md` Priority 1a,
> "the nine α's are the nine normal extremal tracial states of `π(T∞)″`" — is
> **FALSE, and it is refuted by r113 itself.** r113 proves `T∞` has exactly
> **one** tracial state. One ≠ nine. The theorem the framework celebrates as its
> substrate summit is the theorem that kills its own α-mechanism.
>
> **Consequence for the 2026-07-25 audit.** That audit found every purported
> derivation of `α_NP = φ+1/4` to be circular. This audit explains *why*:
> circularity was the only possible outcome. The substrate's invariant set
> contains no irrational number, so any construction that emits `√2` or `φ+1/4`
> must have imported them. The repair is not a better proof — it is naming the
> extra structure honestly.

---

## 1. GROUND TRUTH — what r112/r113 actually establish, and one correction

### 1.1 The construction

`PF/SubstrateBase3Embed.lean:92-96`:

```lean
noncomputable def substrateEmbedMatrix (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ :=
  Matrix.reindex (levelStepEquiv k) (levelStepEquiv k)
    (A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))
```

`A ↦ A ⊗ I₃` — the standard unital multiplicity-3 embedding
`M_{3^k} ↪ M_{3^{k+1}}`. Bundled as a ring hom at
`PF/SubstrateBase3RingHom.lean:64-70`; direct limit at
`PF/SubstrateDirectLimit.lean`; norm completion at
`PF/SubstrateTimelessFieldCompletion.lean`.

### 1.2 The theorems

| Property | Theorem | File:line |
|---|---|---|
| faithful trace | `UHF_trace_faithful` | `PF/SubstrateCompletionFaithful.lean:328` |
| C*-simple | `substrate_completion_simple_unconditional` | `PF/SubstrateCompletionFaithful.lean:367` |
| unique tracial state | `substrate_UHF_trace_unique` | `PF/SubstrateTraceUniqueness.lean:239` |
| trace exists | `uhf_trace_isTracialState` | `PF/SubstrateTraceUniqueness.lean:258` |
| capstone | `r113_substrate_UHF_factor_capstone` | `PF/SubstrateTraceUniqueness.lean:285` |

All kernel-only. I read the proofs; they are correct and the formalization is
genuinely good work.

### 1.3 Correction (documentation, not soundness)

`PF/SubstrateTraceUniqueness.lean:279-281` states the identification argument as:

> "A unital, simple C*-algebra with a unique tracial state that is faithful is
> (the norm closure of) a UHF algebra with a factor tracial state — the Glimm
> `3^∞` UHF factor."

**That inference is invalid.** The irrational rotation algebra `A_θ` and the
reduced free-group C*-algebra `C*_r(F₂)` are both unital, simple, and have a
unique faithful tracial state, and neither is UHF. The conclusion is
nevertheless *true*, for an easier reason: `T∞` is the norm-completion of a
direct limit of `M_{3^k}` along unital multiplicity-3 `*`-homomorphisms, which
**is** the UHF algebra of supernatural number `3^∞` by definition (Glimm's
classification then says it is the unique such). So:

- the identification `T∞ ≅ M_{3^∞}` is **definitional**, not a consequence of
  r112/r113;
- r112/r113 are a from-scratch formalization of standard properties of a
  standard object — valuable as formalization, but they do not *add* any new
  invariant to work with.

Two further terminological notes:
- "**factor**" is a von Neumann notion; `T∞` is a C*-algebra. What is a factor
  is the tracial GNS closure `π_τ(T∞)″ ≅ R`, the hyperfinite **II₁** factor.
- The corpus's own flagship UHF papers already concede that base 3 is
  incidental: `Papers/uhf_faithful_trace_glimm_2026-07-23.tex:333-337` —
  *"every argument below works verbatim in any base ≥ 2"*; same at
  `Papers/glimm_uhf_lean4_2026-07-23.tex:264-266`.

### 1.4 The rigid invariants of `M_{3^∞}` (classical)

| Invariant | Value |
|---|---|
| `K_0` (ordered group with order unit) | `(ℤ[1/3], ℤ[1/3]₊, 1)` |
| `K_1` | `0` |
| tracial state space `T(A)` | one point `{τ}` |
| pairing `ρ : T × K_0 → ℝ` | image exactly `ℤ[1/3]` |
| `τ` on projections | exactly `ℤ[1/3] ∩ [0,1]` |
| Murray–von Neumann semigroup `V(A)` | `ℤ[1/3]₊` |
| Bratteli diagram | one vertex per level, edge multiplicity 3 |
| supernatural number | `3^∞` |
| unital `M_n ↪ A` possible iff | `n` is a power of 3 |
| action of `Aut(A)` on `K_0` | trivial (`Aut(ℤ[1/3], 1) = {id}`) |
| trace-scaling group of `A ⊗ K` | `3^ℤ` |
| `π_τ(A)″` | hyperfinite II₁ factor `R` |
| strongly self-absorbing | `A ⊗ A ≅ A` |

**The whole point of the table: the only real numbers occurring anywhere in it
are the elements of `ℤ[1/3]`, together with `3^ℤ`. Every one of them is
rational.** The corpus already states the `K_0` half of this itself —
`Principia_Fractalis_master_folder/chapters/ch04_timeless_field.tex:380-435`
(Thm 4.16, `K_0(T_∞) ≅ ℤ[1/3]`, `K_1 ≅ 0`, connecting map `n ↦ 3n`), and its
own level-2 box at `:415-422` spells out the trace range:

> "At level `k`, we have `3^k` dimensions, so projections are classified by
> integers `0,1,…,3^k`. Taking the limit and normalizing:
> `dimension/3^k ∈ {0, 1/3^k, 2/3^k, …, 1}`."

**That is exactly the constraint. Nobody in the corpus has ever applied it to
the α-values.** (Verified: exhaustive grep over Lean + LaTeX + markdown for
`K_0`, `ℤ[1/3]`, `trace range`, `Elliott invariant`, `supernatural number`,
`Bratteli` — none of them ever meets an α. The Elliott *classification program*
appears nowhere; every "Elliott" hit in the corpus is the unrelated Elliott
conjecture on multiplicative functions.)

---

## 2. WHAT IS α SUPPOSED TO BE? — six incompatible answers

Answering the task's question 1 requires knowing what object α is. The corpus
gives at least six mutually distinct answers.

| # | Reading | Locus | Verdict against the substrate |
|---|---|---|---|
| 1 | **Phase multiplier**: `R_f(α,s) = Σ_n e^{iπαD₃(n)} n^{-s}` | `ch03_resonance.tex:89-95` (the primary definition) | **α only defined mod 2** — see §5 |
| 2 | **Hausdorff / box-counting dimension** | `ch21_p_vs_np.tex:318-326`, `:1031-1042`; `ch09_spectral_unity.tex:97-101` | ternary self-similarity forbids algebraic irrationals — §6 |
| 3 | **Self-adjointness parameter** of `H_P`, `H_NP` | `ch09_spectral_unity.tex:92-97`; `ch21:253-260` | corpus's own reality condition excludes both — §7 |
| 4 | **Inverse ground-state eigenvalue**, `λ₀ = π/(10α)` | `p_neq_np_spectral.tex:621-628`; `PF/Operators/VAlphaExplicit.lean:305` | vacuous (definition) and refuted (`PolylogViaHilbertSchmidtCompactness.lean:409-465`) |
| 5 | **Extremal tracial state of `π(T∞)″`** — the *only* substrate-intrinsic reading | `millennium_problems_2026-07-09.tex:518-519`; `OPEN_PROBLEMS.md` Prob. 1a | **REFUTED by r113** — §4 |
| 6 | **Fitted numerical parameter** (5-point grid sweep) | `Papers/Data/ForwardPrediction/143_problems_pipeline_2026-07-01_release.py:196-227` | not a mathematical object |

Reading 5 is the only one that is *about* the substrate. It is the one that
r113 destroys.

Readings 1–4 are about an operator or a series, not about the algebra. That is
the escape hatch, and §3 closes it.

---

## 3. THE DICHOTOMY — trace-range vs spectrum

### 3.1 K-theoretic reading: the substrate excludes seven of nine

**Formalized:** `PF/AlphaFromSubstrateKTheory_r123.lean`.

```lean
def MemZ13 (x : ℝ) : Prop := ∃ (m : ℤ) (k : ℕ), x = (m : ℝ) / 3 ^ k
```

`theorem alpha_table_memZ13_verdict` (kernel-only):

| α | value | in `ℤ[1/3]`? | reason for exclusion |
|---|---|---|---|
| `α_Poincaré` | `1` | ✅ | — |
| `α_YM` | `2` | ✅ | — |
| `α_RH` | `3/2` | ❌ | **prime 2** (`3^{k+1} = 2m` is odd = even) |
| `α_P` | `√2` | ❌ | irrational |
| `α_Hodge` | `φ` | ❌ | irrational (`ℚ(√5)`, prime 5) |
| `α_NP` | `φ+1/4` | ❌ | irrational (`ℚ(√5)`, primes 5 and 2) |
| `α_NS` | `3π/2` | ❌ | irrational |
| `α_BSD` | `3π/4` | ❌ | irrational |
| `α_QG` | `√(2π)` | ❌ | irrational |

Supporting theorems, all machine-checked in the new file:

- `substrate_level_projection_trace` — a projection at level `k` has normalized
  trace `card/3^k`. (This is the concrete content of `τ_*(K_0) = ℤ[1/3]`; the
  general statement "every projection of `T∞` is equivalent to a level
  projection" is classical AF theory, cited not formalized.)
- `substrate_attains_every_Z13_trace` — every `m/3^k` with `m ≤ 3^k` is
  attained. The trace range **is** `ℤ[1/3] ∩ [0,1]`, not merely contained in it.
- `not_memZ13_of_irrational`, `not_memZ13_three_halves`, `not_memZ13_one_fifth`.

**The 2-and-5 observation.** `α_RH = 3/2` is the interesting one: it is
*rational* and still excluded. The α-table's denominators are `2` and `4`; its
irrationalities live in `ℚ(√5)` and `ℚ(π)`. The substrate's supernatural number
is `3^∞`, in which **neither 2 nor 5 occurs**. Concretely (all provable from
`τ(p) ∈ ℤ[1/3]`):

- `T∞` has **no projection of trace `1/2`** ⇒ no unital `M₂(ℂ) ↪ T∞`. There is
  no unital qubit in the substrate.
- `T∞` has **no projection of trace `1/5`** (`not_memZ13_one_fifth`) ⇒ no unital
  `M₅(ℂ) ↪ T∞`, and no decomposition `1 = Σ_{i=1}^{5} p_i` into five equivalent
  projections. **The 5-fold icosahedral structure that supplies `φ` and the
  Coxeter number `10 = 2·5` cannot live inside the substrate K-theoretically.**

This last point is the cleanest formulation of the tension between the two
halves of the framework's own story: the substrate is `3^∞`; H₃ is `2·3·5`.

**A confirming numeric.** Under the coupling `λ₀ = π/(10α)`, the only two α's
producing a *rational* λ₀ are the π-built ones:
`λ₀(α_NS) = 1/15`, `λ₀(α_BSD) = 2/15`. Neither is in `ℤ[1/3]` — the `5` in `15`
blocks it. Had the coupling denominator been `9 = 3²` instead of `10 = 2·5`,
they would be `2/27` and `4/27`, both **in** `ℤ[1/3]`. (Verified to 50 digits
with mpmath.) *Labelled as an observation, not a derivation.* But it is a
precise statement of the mismatch: the coupling constant is pentagonal where the
substrate is ternary.

### 3.2 Spectral reading: the substrate constrains nothing

`theorem substrate_level_realizes_arbitrary_spectrum {k : ℕ} (a : Fin (3^k) → ℝ)`
— for *any* assignment of reals, `Matrix.diagonal (a ·)` is Hermitian and its
spectrum is exactly `range a` (`spectrum_diagonal`). At `k = 2` that is `M₉`,
which sits unitally inside `T∞`.

`theorem two_distinct_alpha_assignments_both_realized` — the framework's nine
α-values and *any* distinct nine-tuple are both realized, inside the same
`M₉ ⊆ T∞`, as spectra of self-adjoint elements. This is the explicit
"two distinct α-assignments consistent with every substrate-derived invariant"
that the task asked for.

The same holds a fortiori for unbounded operators affiliated to `T∞`, and for
operator norms: none of these is constrained by the algebra.

### 3.3 The dichotomy stated

> Let `X` be any quantity attached to `T∞`.
>
> - If `X` is **K-theoretic/tracial** — `τ(p)` for a projection, a `K_0` class,
>   a trace-scaling factor, an index — then `X ∈ ℤ[1/3]` (resp. `3^ℤ`), hence
>   `X ∈ ℚ`. Seven of the nine α-values are then **excluded**.
> - If `X` is **spectral** — an eigenvalue, spectral value, or norm of an
>   element (bounded or affiliated) — then `X` ranges over **all** of `ℝ` and
>   the substrate says **nothing**.
>
> There is no third kind of quantity in the Elliott invariant. Hence the
> substrate cannot single out `√2` or `φ + 1/4`.

**The only canonical irrational the substrate produces is `log 3 ≈ 1.09861`**
(Connes entropy of the shift; equivalently the growth rate of the Bratteli
diagram; `2 log 3` for the index of the level inclusion). Checked numerically
(mpmath, 60 dps): PSLQ over `{α, log 3, 1}` with coefficients up to `10^6`
finds a relation **only** for the three rational α's (`1`, `3/2`, `2`), and in
each case the `log 3` coefficient is `0`. No α is `3^{p/q}` for any rational of
height `≤ 10^5`. Nearest matches are not close:

| α | nearest simple base-3 constant | gap |
|---|---|---|
| `√2 = 1.41421` | `3^{1/3} = 1.44225` | `2.8 × 10⁻²` |
| `φ = 1.61803` | `log 3/log 2 = 1.58496` | `3.3 × 10⁻²` |
| `φ+1/4 = 1.86803` | `3^{3/5} = 1.93318` | `6.5 × 10⁻²` |
| `√(2π) = 2.50663` | `8/3 = 2.66667` | `1.6 × 10⁻¹` |

Negative, and clean.

---

## 4. THE SHARPEST RESULT — Conjecture 8.X.2 is false, and r113 kills it

### 4.1 The claim

`Papers/principia_fractalis_millennium_problems_2026-07-09.tex:518-519`,
`\begin{conjecture}[Extremal-trace uniqueness of the projective-limit substrate]`
`\label{conj:extremal-trace}`:

> "Let `π : T_∞ → B(H)` be its GNS representation on the framework's canonical
> Hilbert space. Let `π(T_∞)''` denote the double-commutant. **Then the space of
> normal extremal tracial states on `π(T_∞)''` is finite and isomorphic to the
> 9-element set `{α_i}_{i=1}^9`** … under the Dixmier trace functional."

Sharpened at `:531-533`:

> "The finite-dimensional center of `π(T_∞)''` under the base-3
> fundamental-group action has exactly 9 minimal projections, each carrying a
> distinct extremal tracial weight matching one `α_i`."

Catalogued as `OPEN_PROBLEMS.md` **Priority 1a — the corpus's #1 open problem**,
restated in `Papers/principia_fractalis_alpha_skeleton_2026-07-13.tex:163`
(*"The operator-algebra closure identifying the nine α-values as the extremal
tracial states of `π(T∞)″`"*), and decomposed into (C1)–(C8) in
`PF/ExtremalTraceUniquenessProofPlan.lean:92, 108, 127`.

**This is the only place in the entire corpus where the α-values are given a
definition intrinsic to the substrate.** Everything else defines them by fiat
and checks consistency.

### 4.2 The refutation

**(R1) The premise is wrong.** The conjecture's proof-sketch
(`:522`) says `T_∞` "is expected to yield a Type III₁ hyperfinite factor", and
`OPEN_PROBLEMS.md:39-45` builds the whole attack plan on that. **r112 proves
`T∞` has a faithful tracial state** (`UHF_trace_faithful`). A type III factor
admits no nonzero normal semifinite trace at all. `π_τ(T∞)″` is the hyperfinite
**II₁** factor `R`. Sub-conjecture (C2) ("classical Connes classification of
Type III₁ hyperfinite factors") is therefore attacking a nonexistent object.

**(R2) The escape hatch is closed.** `OPEN_PROBLEMS.md:41-45` is candid:
*"Type III₁ typically has unique trace — BAD for the 9-values directly. However,
if the fundamental group of the base-3 Cantor set is non-trivial … the algebra
can admit a finite-dimensional center with exactly 9 extremal states."*
**r113 closes that door regardless of the type.** Formalized in the new file:

```lean
theorem no_nine_distinct_tracial_states :
    ¬ ∃ f : Fin 9 → (TimelessFieldCompletion → ℂ),
        (∀ i, IsTracialState (f i)) ∧ Function.Injective f
```

with the positive form
`substrate_tracial_state_space_singleton : ∀ φ, IsTracialState φ → φ = UHF_trace`.

**(R3) The von Neumann statement, in every representation.** (Classical, stated
here with proof, not formalized — mathlib has no von Neumann algebra theory of
this depth.)

> **Proposition.** For every nonzero representation `π` of `T∞`, the von Neumann
> algebra `π(T∞)″` admits **at most one** normal tracial state.
>
> *Proof.* `T∞` is simple (r112), so `π` is faithful. Let `ω` be a normal tracial
> state on `π(T∞)″`. Then `ω ∘ π` is a state on `T∞` (states on C*-algebras are
> automatically norm-continuous), it is additive and ℂ-homogeneous, unital, and
> tracial — i.e. `IsTracialState (ω ∘ π)` in the sense of
> `SubstrateTraceUniqueness.lean:164`. By r113, `ω ∘ π = τ_UHF`. Now `π(T∞)` is
> σ-weakly dense in `π(T∞)″` and `ω` is σ-weakly continuous, so `ω` is determined
> by `ω|_{π(T∞)}`. Hence any two normal tracial states on `π(T∞)″` agree. ∎
>
> **Corollary.** `π(T∞)″` has either 0 or 1 normal tracial states, never 9.
> Conjecture 8.X.2 is false in every representation.

**(R4) The two clauses of the conjecture are mutually incompatible anyway.** The
conjecture says "normal extremal tracial states … *under the Dixmier trace
functional*". Dixmier traces are singular by construction (they vanish on
finite-rank operators) and are therefore **not normal**. Whichever clause is
intended, the other is wrong.

### 4.3 What this costs the framework

`OPEN_PROBLEMS.md` Priority 1a is not merely open — it is **closed negative**.
The eight sub-conjectures (C1)–(C8) cannot be discharged as stated: (C2) has no
object, (C4)/(C5)/(C6) ("finite-dimensional center", "9 minimal central
projections", "extremal traces ↔ minimal projections") are false for a factor,
and the master conjecture is refuted by (R3).

This is *good* news for the corpus's honesty ledger and *bad* news for the
α-story. It should be recorded as such, not quietly retired.

---

## 5. α IS ONLY DEFINED MOD 2 — the α-skeleton is not well-posed

The framework's primary definition of α
(`ch03_resonance.tex:89-95`, `def:fractal-resonance`):

```
R_f(α, s) = Σ_{n=1}^∞ e^{iπ α D₃(n)} / n^s
```

`D₃(n) ∈ ℕ`. Therefore `R_f(α+2, s) = R_f(α, s)` identically:

```lean
theorem resonance_phase_two_periodic (α : ℝ) (d : ℕ) :
    Complex.exp (Real.pi * (α + 2) * d * Complex.I)
      = Complex.exp (Real.pi * α * d * Complex.I)
```

**α is a point of `ℝ/2ℤ`, not of `ℝ`.** Consequences:

1. Any claim of the form "the substrate forces `α = √2`" can at best mean
   "forces `α ≡ √2 (mod 2)`".
2. **The α-skeleton's algebraic invariants are not gauge-invariant.** Clause (1)
   of the capstone, `α_P² = α_YM` (`CrossMillenniumSharedInvariants.lean:95`),
   fails under the shift:

```lean
theorem alpha_P_sq_eq_alpha_YM_not_mod_two_invariant :
    ¬ ∃ m : ℤ, (Real.sqrt 2 + 2) ^ 2 = 2 + 2 * (m : ℝ)
```

   `(√2+2)² = 6 + 4√2 ≈ 11.657`, which is not `2 mod 2ℤ`. Same for `α_NS = 2·α_BSD`,
   `α_RH · α_YM = 3`, and `α_NP − α_Hodge = 1/4`: all of them are statements
   about chosen *representatives*, not about the resonance parameters they claim
   to constrain. The "algebraic skeleton" of
   `cross_millennium_shared_invariants_capstone` is therefore not a statement
   about `R_f` at all.
3. `α_YM = 2 ≡ 0`, and `e^{2πiD₃(n)} = 1` for all `n`, so **`R_f(α_YM, s) = ζ(s)`
   exactly** — the Yang-Mills α is the value at which the framework's own
   resonance function degenerates to the plain Riemann zeta function, i.e. it is
   what `ch07_constants.tex:236` itself calls "Trivial Resonance (no resonance)".

This is independent of the substrate and, as far as I can find, unrecorded
anywhere in the corpus.

---

## 6. THE HAUSDORFF-DIMENSION READING

`WeightedDigitalSumGeneratingFunction.lean:139-143` and
`ch21_p_vs_np.tex:318-326` both declare `d_H(K_P) = √2`;
`ch21:1031-1042` and `ch09_spectral_unity.tex:97-101` declare
`dim_frac(P) = √2`, `dim_frac(NP) = φ + 1/4`.

**Constraint from ternary self-similarity.** Let `K` be self-similar under an
IFS satisfying OSC whose contraction ratios are all `3^{-k}` (the natural
self-similarity of a base-3 substrate), with `N` maps. Moran's equation
(`PF/TuringEncoding/IFSHausdorffDimensionInfrastructure.lean:112` has the
identity `N·r^d = 1`) gives

```
    d = log N / (k log 3),     i.e.   3^{kd} = N ∈ ℕ.
```

- If `d` is **irrational algebraic**, `3^{kd}` is transcendental by
  **Gelfond–Schneider** (`3` algebraic ≠ 0,1; `kd` irrational algebraic), hence
  not an integer. **Contradiction.**
- Therefore **`√2`, `φ`, and `φ+1/4` are all impossible** as dimensions of a
  ternary equal-ratio self-similar set. (Achievable irrational dimensions are
  exactly `log_3 N / k` for `N` not a power of 3 — e.g. `log 2/log 3 = 0.63093`,
  the Cantor value the corpus computes at
  `PF/MillenniumSixReductions.lean:190`. Those are all transcendental, never
  algebraic.)
- `k = 1` case is elementary and needs no Gelfond–Schneider: `4 < 3^{√2} < 5`
  (`3^{√2} = 4.72880…`, verified to 50 digits), so `3^{√2} ∉ ℕ`.

Gelfond–Schneider is not in mathlib, so this branch is stated with proof rather
than formalized. It is nevertheless a genuine obstruction, and it is *conditional
on the fractal being the substrate's own*: `ch21`'s `K_P` is never constructed,
so strictly it is only a constraint on the reading, not a refutation of the text.
**Note however that `ch21:319` does not derive `d_H = √2` from any IFS — it
*sets* `d_H := α_P`.** So the dimension reading is a restatement of the α-pin,
not an independent source for it.

Two further unconditional internal problems in the dimension reading:

- **`ch22_navier_stokes.tex:175`** states `α = 3 − d_H` (α as a helicity-measure
  singularity exponent). With `α_NS = 3π/2 = 4.712` (asserted at `ch22:9`), this
  forces `d_H = −1.712 < 0`. **Negative Hausdorff dimension.** The same chapter
  carries both statements. (`ch22:514` is honest that `α = 3π/2` is
  "ASSERTED / EMPIRICAL … neither derived nor experimentally validated".)
- `α_NS = 4.712`, `α_QG = 2.507`, `α_BSD = 2.356` cannot be dimensions of the
  same "language space" objects for which `α_P = 1.414`; the dimension reading
  is only ever offered for the P/NP pair and is silently abandoned elsewhere.

---

## 7. THE π/10 THREAD — worked exactly, and it is empty

This was the task's most promising visible lead. It does not close.

### 7.1 The algebra

`sin(π/10) = 1/(2φ)` is genuine and correctly proved
(`PF/H3CoxeterOrigin.lean:114` `sin_pi_div_ten`, `:199`
`sin_pi_div_ten_eq_inv_two_phi` — the one substantive theorem in that file).

The universal coupling is **a definition**, everywhere in the corpus:

```lean
-- PF/UniversalAlphaOperatorFamily.lean:95
noncomputable def lambda0 (H : HAlphaUniversal) : ℝ := pi_10 / H.alpha
-- PF/Operators/VAlphaExplicit.lean:305
noncomputable def groundStateValue (α : ℝ) : ℝ := Real.pi / (10 * α)
-- PF/SpectralIsolationSubstrateDischarge.lean:100  — proved by `rfl`
theorem substrate_lambda_universal_coupling (i : Fin 9) :
    substrate_lambda_skeleton i = Real.pi / (10 * substrate_alpha_skeleton i) := rfl
```

So `λ₀(α)·α = π/10` is `(π/10/α)·α = π/10`, closed by `field_simp`. Composing
with the H₃ identity gives, in the new file:

```lean
theorem coupling_H3_identity_holds_for_every_alpha (α : ℝ) (hα : α ≠ 0) :
    Real.sin (lambda0 α * α) = 1 / (2 * Real.goldenRatio)
```

**Universally quantified over α.** The "same π/10 appears in both" observation
is the observation that `π/10` appears on both sides of an identity that is
uniform in α. It produces neither `φ` nor `φ+1/4` nor anything else. **The thread
is closed, negatively, and now machine-checked to be closed.**

### 7.2 Things I checked and rejected (all fits, all reported as fits)

- **Self-consistency `λ₀ = α`** ⇒ `α² = π/10` ⇒ `α = 0.56050…`. Not an α.
- **`λ₀ = sin(π/10) = 1/(2φ)`** ⇒ `α = πφ/5 = 1.01664…`. Not an α (and not `1`).
- **`λ₀ = 2sin(π/10) = 1/φ`** ⇒ `α = πφ/10 = 0.50832…`. Not an α.
- **The `+1/4` as pentagonal data.** `1/4 = cos(π/5)·cos(2π/5)` exactly (this is
  already in the corpus at `H3CoxeterOrigin.lean:403`), so
  `φ + 1/4 = cos(π/5)·(2 + cos(2π/5))`, verified to 60 digits. This *slightly*
  improves on the 2026-07-25 audit's "the `+1/4` has no motivation" — the number
  `1/4` **is** pentagonal. **But it is still a fit**: nothing selects the
  combining rule "add the product of the two pentagon cosines to twice the
  first". `φ + 4`, `φ/4`, `4φ`, `φ + 1/10` are equally expressible.
- **The quadratic is the golden equation in disguise.**
  `16α² − 24α − 11 = 16·((α−1/4)² − (α−1/4) − 1)` — exact, verified. So
  "the quadratic forces `φ + 1/4`" and "`α − 1/4 = φ`" carry literally the same
  information (confirming `ALPHA_NP_DERIVABILITY_2026-07-25.md` §1.3).
- **`α_QG` fixed point.** `α = 20·λ₀(α) = 2π/α ⇒ α² = 2π`
  (`millennium_problems_2026-07-09.tex:534`). The fixed point of `x ↦ c/x` is
  `√c` for *any* `c`; the multiplier `20 = 2·10` is what produces `2π`. A fit.

### 7.3 Where the "10" comes from — four mutually incompatible stories

For the record, since the task's premise ("the same π/10 appears in both") rests
on the 10 being substrate-derived:

| Story | Locus | Problem |
|---|---|---|
| (A) H₃ Coxeter number `h(H₃) = 10` | `PF/H3CoxeterOrigin.lean:75, 99` | `H3_Coxeter_number : ℕ := 10` is a hand-entered numeral; the "theorem" is `2x/10/2 = x/10`. The paper's own §
 concedes it is *"a structural resonance … **not a derivation**"* (`millennium_problems_2026-07-05.tex:398-400`) |
| (B) `10 = α_YM · α_HN = 2 · 5` | `PF/Referee/MinimalRigidityForcesH3CombinatorialStructure.lean:75` | circular — `α_YM := 2` is a def; and it *reverses* the direction of (A) |
| (C) base-3: "`10₃ = 3₁₀`" | `ch09_spectral_unity.tex:255, 412` | a notation pun; incompatible with (A)/(B), which need the integer ten |
| (D) decimal / Shannon bins | `ch07_constants.tex:98, 131-135` | *"we use decimal notation … 10 bins (digits 0–9)"* — incompatible with a base-3 framework |

And the corpus's own experiment falsified (A):
`ARCHIVE/2026-06-08-cleanup/dirs/experimental/h3_icosahedral_substrate/results/VERDICT_2026-05-24.md:19`
— *"the structural hypothesis 'only I₂(10) produces π/(10·α) by Coxeter number'
FAILS. I₂(8) at α=φ gives V-only gap 0.001 — better than I₂(10). **The '10' is
not coming from Coxeter number h alone.**"*

---

## 8. BASE-3 RIGIDITY — what actually depends on the 3

| Item | Depends on 3? | Evidence |
|---|---|---|
| Radix economy `Q(b) = ln b / b`, integer-optimal at 3 | proven, **but a leaf** | `PF/RadixEconomy.lean`; three importers (`PF.lean:30`, `PF/Analytic/FractalDomain.lean:53`, `PF/Referee/FractalMathematicsCore.lean:31`), **all comment-only**. Zero downstream theorem uses. Coq mirror is `Theorem ternary_optimality : True.` (`PF_Coq_Code/PF/RadixEconomyCoq.v:55`) |
| `digitalSum3` | hard-coded 3 | `PF/TuringEncoding/Basic.lean:70` |
| D₃ algebrization defeat | **base-generic** for `b ≥ 2` | `PF/TuringEncoding/D3NonAlgebraic.lean:64,116,186`; the proof only uses `D_b(b^k)=1`, `D_b(b^k−1)=(b−1)k` |
| Substrate tower `A ↦ A ⊗ I₃` | **authors state base-irrelevant** | `Papers/uhf_faithful_trace_glimm_2026-07-23.tex:333-337` |
| Trace preservation | any multiplicity | `PF/SubstrateUHFPreTraceDirectLimit.lean:95,103` |
| NS cascade `Σ(2/3)^n` | needs `S > 2`; 3 is just the smallest integer | `PF/NSBase3SelfSimilarity.lean:14-24` |
| `K_0 ≅ ℤ[1/3]` | **yes** — but a hand-built model, honest-scoped | `PF/Consciousness/TimelessFieldKTheoryUpgrade.lean:12, 42-44, 96` |
| **The nine α-values** | **NO** | `PF/FrameworkApplicationCapstone.lean:55-63` — not one references base 3. Zero `Alpha*.lean` file imports any `PF.Substrate*` |
| `V_α` operator (contains `D̂₃`) | yes — the *only* α↔3 link | `PF/Operators/VAlphaExplicit.lean:131,157`; and the α↔spectrum step there is a named open input (`KatoRellichInput`) |

**Answer to task item 4:** the supernatural number `3^∞` constrains the α-values
in exactly one way — via `ℤ[1/3]` (§3.1) — and that constraint **excludes** seven
of the nine. Nothing else about base 3 reaches the α-table. Even the theorem the
framework cites as the reason for base 3 (`ternary_optimality`) has no consumers.

The one place `RadixEconomy` is invoked as justification is prose only:
`millennium_problems_2026-07-08.tex:1325` (`ln 3` in the Higgs mass), whose own
next line concedes *"The substrate mechanism … has not yet been constructed."*

---

## 9. THE ONE POSITIVE CONVERGENCE

The corpus's own machine-checked negative result and the substrate's K-theory
**agree**, by completely independent routes.

`bare_route_structural_finding`
(`PF/TuringEncoding/WeightedDigitalSumGeneratingFunction.lean:131-134`) proves
the reality condition on the ternary generating function admits only
`sin(πα) = 0` or `cos(πα) = −1/2`, i.e.

```
    α ∈ ℤ    or    α ∈ ±2/3 + 2ℤ.
```

New theorem (`AlphaFromSubstrateKTheory_r123.lean`):

```lean
theorem bare_route_alpha_memZ13 (α : ℝ) (h : betaIm α = 0) : MemZ13 α
```

**Every α admitted by the ternary reality condition lies in `ℤ[1/3]`** — the
same set the substrate's `K_0` produces. Two independent substrate-side
computations converge on "α is a 3-adic rational", and both exclude `√2` and
`φ + 1/4`:

```lean
theorem canonical_alphas_fail_bare_route : betaIm α_P ≠ 0 ∧ betaIm α_NP ≠ 0
```

This is the strongest *positive* thing the substrate says about α, and it says
the framework's headline values are wrong. It is also, I think, the most
publishable single item in this whole area: *two independent invariants of the
same ternary substrate agree on the arithmetic type of α, and the corpus's
α-table violates both.*

---

## 10. THE MAP — what is forced, what is not

### 10.1 NOW PROVABLE (consequences of r112/r113 + classical `M_{3^∞}` theory)

| # | Statement | Status |
|---|---|---|
| 1 | `T∞` has exactly one tracial state | **theorem** (r113) |
| 2 | `T∞` is simple, faithfully traced | **theorem** (r112) |
| 3 | `τ` on level-`k` projections `= m/3^k`, all attained | **theorem** (r123 §2) |
| 4 | `τ_*(K_0(T∞)) = ℤ[1/3]`; `K_1 = 0` | classical (Glimm); corpus states it at `ch04:380-435`, models it at `TimelessFieldKTheoryUpgrade.lean` |
| 5 | Every number in the Elliott invariant of `T∞` is rational | classical, from 4 |
| 6 | No projection of trace `1/2` or `1/5`; no unital `M₂` or `M₅` in `T∞` | **theorem** from 3–4 (arithmetic core formalized: `not_memZ13_one_fifth`) |
| 7 | `π_τ(T∞)″ ≅` hyperfinite II₁ factor `R` (NOT type III₁) | classical, from 1–2 |
| 8 | `π(T∞)″` has ≤ 1 normal tracial state, in every representation | **theorem** (§4.2 R3) |
| 9 | Every finite real tuple is the spectrum of a s.a. element of `M_{3^k} ⊆ T∞` | **theorem** (r123 §4) |
| 10 | `Aut(T∞)` acts trivially on `K_0` and preserves `τ` | classical |
| 11 | Trace-scaling group of `T∞ ⊗ K` is `3^ℤ` | classical |
| 12 | `T∞ ⊗ T∞ ≅ T∞` (strongly self-absorbing) | classical |
| 13 | Bratteli diagram: one vertex/level, multiplicity 3 | by construction |

### 10.2 NOW REFUTED

| # | Framework claim | Killed by |
|---|---|---|
| R1 | Conjecture 8.X.2: 9 normal extremal tracial states of `π(T∞)″` ↔ the 9 α's (`OPEN_PROBLEMS.md` Prob. 1a; `millennium_problems_2026-07-09.tex:518`) | r113 + §4.2 |
| R2 | (C2) "Connes classification of Type III₁ hyperfinite factors" applies to `T∞` (`OPEN_PROBLEMS.md:39-45`) | r112 (faithful trace ⇒ not type III) |
| R3 | (C4)/(C5)/(C6) finite-dimensional center with 9 minimal central projections | `π_τ(T∞)″` is a factor |
| R4 | "the substrate forces `α_NP = φ+1/4`" (`millennium_problems_2026-07-13.tex:160, 361, 926, 1295`) | §3 dichotomy: the substrate cannot force any irrational |
| R5 | `α_P = √2` as the Hausdorff dimension of a ternary self-similar set (`WeightedDigitalSum…:141`) | Gelfond–Schneider, §6 |
| R6 | `α = 3 − d_H` together with `α_NS = 3π/2` (`ch22:175` vs `ch22:9`) | forces `d_H < 0` |
| R7 | The α-skeleton as a statement about resonance parameters | 2-periodicity, §5 |

### 10.3 STILL INDEPENDENT OF THE SUBSTRATE (assertions, unaffected either way)

Everything about `H_α`, `V_α`, `T̃₃^sym`, the choice of `π/10`, and the nine
α-values themselves. The substrate is silent on all of it — which is precisely
the point.

### 10.4 THE α-VALUES: which bucket?

**Neither.** They are not among the substrate-determined quantities (§10.1),
because seven of them are irrational and the substrate's invariant is rational.
They are not "still open pending more work on the substrate", because §3.3 shows
no amount of substrate work can reach them. They belong to a third category the
corpus does not currently have: **data of a chosen operator, imported from
outside the substrate.**

---

## 11. WHY THE CIRCULARITY WAS INEVITABLE

`codex/ALPHA_NP_DERIVABILITY_2026-07-25.md` documented three closed loops and
concluded "asserted, not derived". This audit strengthens that from a contingent
finding to a structural one:

> **The substrate's complete classifying invariant contains no irrational
> number. `√2`, `φ`, and `φ+1/4` are irrational. Therefore no derivation of
> them from substrate invariants exists — not "has not been found", but
> *cannot exist*. Any construction that emits them must have introduced them as
> data. `p_neq_np_spectral.tex:589` introducing `π/(10(φ+1/4))` into `w_NP` is
> not a drafting slip that a more careful author would avoid; it is the only way
> the number can get in.**

That reframes the repair. The corpus should stop trying to derive the α's from
`T∞` and instead state plainly: *the α-values are parameters of a chosen
operator family on the substrate, not invariants of the substrate.* That is a
defensible, honest, and still-interesting position. The current position is not
reachable.

---

## 12. THE NEW LEAN FILE

`PF_Lean4_Code/PF/AlphaFromSubstrateKTheory_r123.lean` — builds clean
(`lake build PF.AlphaFromSubstrateKTheory_r123` → *Build completed successfully*),
zero `sorry`, zero project axioms, all 17 audited declarations
`[propext, Classical.choice, Quot.sound]`.

| Theorem | Content |
|---|---|
| `phi_eq_goldenRatio` | corpus `phi` = mathlib `Real.goldenRatio` |
| `MemZ13`, `memZ13_isRat` | `ℤ[1/3]` and its rationality |
| `not_memZ13_of_irrational` | irrationality exclusion |
| `not_memZ13_three_halves` | the prime 2 (kills `α_RH = 3/2`) |
| `not_memZ13_one_fifth` | the prime 5 (kills unital `M₅ ↪ T∞`) |
| `substrate_level_projection_trace` | `τ(P) = card/3^k` |
| `substrate_attains_every_Z13_trace` | trace range is exactly `ℤ[1/3] ∩ [0,1]` |
| **`alpha_table_memZ13_verdict`** | **2 of 9 in, 7 of 9 out** |
| `substrate_level_realizes_arbitrary_spectrum` | every real tuple is a substrate spectrum |
| `two_distinct_alpha_assignments_both_realized` | the explicit impossibility witness |
| `substrate_tracial_state_unique_pairwise` | r113, pairwise form |
| **`no_nine_distinct_tracial_states`** | **Conjecture 8.X.2 is false** |
| `substrate_tracial_state_space_singleton` | positive form |
| **`coupling_H3_identity_holds_for_every_alpha`** | **the π/10 thread is vacuous** |
| `resonance_phase_two_periodic` | α lives in `ℝ/2ℤ` |
| `alpha_P_sq_eq_alpha_YM_not_mod_two_invariant` | the skeleton is not gauge-invariant |
| **`bare_route_alpha_memZ13`** | **the corpus's own ternary route also forces `ℤ[1/3]`** |
| `canonical_alphas_fail_bare_route` | `√2` and `φ+1/4` fail it |
| `r123_substrate_cannot_force_alpha_capstone` | (A)–(F) bundled |

**What is NOT formalized, and is flagged as such in the file's honest-scope
block:** operator K-theory (`MemZ13` is an elementary predicate, not
`K_0`); "every projection of `T∞` is equivalent to a level projection"
(classical AF theory); the von Neumann corollary of §4.2 (mathlib lacks the
theory); Gelfond–Schneider (§6).

---

## 13. RECOMMENDED ACTIONS

1. **Record Conjecture 8.X.2 / `OPEN_PROBLEMS.md` Priority 1a as REFUTED**, with
   the r113 citation. Do not leave the corpus's #1 open problem listed as open
   when its own summit theorem closes it negatively. Publishing this is a
   credibility gain, not a loss.
2. **Correct `SubstrateTraceUniqueness.lean:279-281`.** The stated inference
   (unique faithful trace + simple ⇒ UHF `3^∞`) is invalid; give the correct
   reason (the tower is UHF by construction; Glimm classifies it).
3. **Replace "the substrate forces `α_NP = φ+1/4`"** (`…2026-07-13.tex:160, 361,
   926, 1295`) with the honest statement: *the substrate's invariant is
   `ℤ[1/3] ⊂ ℚ`; the α-values are parameters of a chosen operator family, not
   substrate invariants.*
4. **Promote §9.** "Two independent invariants of the ternary substrate — its
   `K_0` and its own generating function's reality condition — both force
   `α ∈ ℤ[1/3]`, and both exclude the framework's headline values" is a real,
   self-contained, publishable result, and it is now fully machine-checked.
5. **Fix `ch22`.** `α = 3 − d_H` (`:175`) and `α_NS = 3π/2` (`:9`) cannot both
   stand.
6. **Add the mod-2 caveat to `CrossMillenniumSharedInvariants.lean`.** Its
   invariants are statements about representatives; the file should say so.
7. **Retire the `Type III₁` language** everywhere (`OPEN_PROBLEMS.md:39-45`,
   `principia_fractalis_2026-07-09_v2.tex:287, 314, 325`,
   `…_v3.tex:327, 339`, `…2026-07-10_v3.tex:330, 342`,
   `ExtremalTraceUniquenessProofPlan.lean` (C2)). r112 makes it impossible.

---

## 14. SUMMARY TABLE

| Question asked | Answer | Evidence |
|---|---|---|
| Are the α's trace values? | **No** — 7 of 9 are irrational, `α_RH` fails 2-adically | `alpha_table_memZ13_verdict` |
| Is that a contradiction with the framework's claims? | **Yes**, for the trace/K-theory reading; and Conjecture 8.X.2 is outright refuted | §3.1, §4 |
| Or irrelevant because α is spectral data? | The reading is available but **vacuous** — every real is a substrate spectral value | `substrate_level_realizes_arbitrary_spectrum` |
| Does `ℤ[1/3]` force the α's to arise some other way? | It forces them to arise **outside the substrate** | §3.3, §11 |
| What does the proven substrate force? | 13 items, all rational or structural | §10.1 |
| Does the π/10 + H₃ thread produce `φ`? `φ+1/4`? | **Neither.** The combined identity holds for every α | `coupling_H3_identity_holds_for_every_alpha` |
| Does base 3 / `3^∞` constrain the α's? | Only via `ℤ[1/3]` — and that **excludes** 7 of 9 | §8 |
| Derivation found? | **No** (and none can exist) | §11 |
| Impossibility found? | **Yes**, formalized | `r123_substrate_cannot_force_alpha_capstone` |

---

*Audit performed 2026-07-26. Read-only except for the one new Lean file, which
adds no dependency to any existing file. All numerics verified with mpmath at
50–60 decimal places. No git operations performed.*

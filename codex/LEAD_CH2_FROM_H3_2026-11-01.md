# CLOSED 2026-11-02 — the ch₂-from-H₃ route, and the false absence claim it rested on

**Status: route CLOSED. One claim in the original was false and had propagated
into the manuscript. Four independent attacks returned; all four closed it.**

The original lead (2026-11-01, commit `9b139eff`) proposed that the `20` in
`ch₂ = 19/20` might come from the icosahedral group H₃ independently of `0.95`,
which would have collapsed the consciousness threshold and the universal
coupling `π/10` into one group-theoretic fact. It set its own closing condition:
*"if the saturation value provably is not 20, the route closes and that is also
progress."* That condition was met, and more.

## The false claim, and how I made it

The lead stated: *"nothing in the Lean corpus connects 20, 400 or
Phi_threshold to H₃ or to the icosahedron."*

**The load-bearing half is false.** `PF/HodgeCrystallizationH3Discharge.lean:168`

```lean
theorem hodge_rank_witness_H3 :
    (20 : ℕ) = 2 * H3_Coxeter_number := by
  show (20 : ℕ) = 2 * 10
  norm_num
```

dated **2026-05-24**, importing `PF.H3CoxeterOrigin`, bundled at `:211`, carried
in the master manifest at `PF.lean:733`.

**How the error happened, exactly.** My verification script grepped for
`2 \* H3_Coxeter_number` and *printed the matching filename*. The script's next
line was a hardcoded label reading `(empty = no such link found)`. I read the
label instead of the data directly above it. This is not a grep-scope failure —
the grep worked. It is a reading failure, and the lesson is narrower and worse
than "try several namings": **never pair a search with a pre-written conclusion
about its result.** The label must be computed from the output or omitted.

The `400` and `Phi_threshold` halves of the absence claim are true — no file
connects those to H₃.

## And the existing identity runs backwards

`HodgeCrystallizationH3Discharge.lean:166` documents its own direction: *"The
Hankel-rank ceiling `20 = 1/(1 − σ_c) = 1/(1 − 19/20)`"*, and
`PF/MillenniumSixReductions.lean:761` proves
`low_rank_bound_at_sigma_c : 1/(1 − sigma_c) = 20` with `sigma_c := 19/20`. So
the corpus's `20 = 2h(H₃)` takes its 20 **from** 0.95 — the identical
circularity the lead correctly diagnosed for `Phi_threshold`. The ground was
already walked, already committed, and already circular.

## The four refutations

**1. The measure has no saturation value.** `Phi_IIT := 2 * vNEntropy`
(`PF/Consciousness/Ch2PhiBridgeDischarge.lean:116`) on `SchmidtSpectrum n` has
supremum `2 log n` at fixed `n`, attained at the uniform spectrum, and `+∞`
overall. The corpus's own link theorem `:413` fixes the 20 as
`uniformSchmidt 19` — the Hilbert-space **dimension input**. What saturates is
the bridge `1 − exp(−Φ/2)`, and it saturates at **1**, not 0.95. The lead's
target had no referent.

**2. The groups don't permit the collapse.** The substrate's only canonical
action is `A₅ ⊂ SO(3) ⊂ SU(3)` on `M₃(ℂ)` by conjugation, which factors through
`PO(3)` and kills the central `{±I}`. So the substrate sees only
`A₅ = W(H₃)/{±I}`. The Coxeter element of H₃ is **improper** (det = −1), and
**A₅ has no element of order 10** — verified by exhaustive enumeration: orders
are exactly `{1,2,3,5}`. So the substrate-visible half-argument is `π/5`, not
`π/10`. The 20 is an A₅ index (`[A₅ : Sylow₃] = 20`, while
`[W(H₃) : Sylow₃] = 40`); the 10 of π/10 needs W(H₃)'s improper element. They
sit on opposite sides of the centre and cannot collapse.

**3. The specificity test was the wrong test.** Twelve H₃/icosahedral/A₅
invariants lie in `[10,100]` — 10, 12, 15, 18, 20, 24, 30, 31, 32, 59, 60, 62 —
each giving an exact `1 − 1/N`, covering `[0.900, 0.9839]` with maximum gap
**0.0167**. Verified: every two-decimal threshold from 0.90 to 0.99 is within
0.01 of one. And 0.90 would have been *cleaner* — `1 − 1/h(H₃)`, no factor of
two. Separately, 16 depth-1 expressions over the corpus's own published H₃
integer pool hit 20 exactly, and 978 at depth 2. `codex/ADVERSARIAL_ALPHA_2026-10-02.md:116-132`
had already published that pool *including 20*, with the verdict *"individually
correct and carry essentially no information."* The lead contradicted a
month-old ruling of its own corpus.

**4. The supporting table was one fact.** `|W| = d₁d₂d₃` with `d₁ = 2` always,
so `|W|/d₂ = d₁d₃ = 2h` for **every** rank-3 Coxeter group — verified: A₃
`24/3 = 8 = 2·4`, B₃ `48/4 = 12 = 2·6`, H₃ `120/6 = 20 = 2·10`. Zero
H₃-specific content. Faces = dual vertices is duality. Four rows read as four
corroborations; it was one.

Also: other groups supply 20 more canonically. `I₂(10)` has `|W| = 20 = 2h` with
`h = 10`, and `|W| = 2h` is a *theorem* for every rank-2 dihedral group. `A₄`
has `|roots| = nh = 20`. `H₄` and `E₈` carry 20 as a **degree** with 19 as its
matching exponent, so `19/20 = mᵢ/dᵢ` directly, with no saturation functional
form required at all.

## Two corrections against the lead's own framing

**The exactness comparison was invalid.** `Φ = 2 log X` gives
`1 − e^{−Φ/2} = 1 − 1/X` identically — the `2` and the `/2` cancel. So **400 is
never a quantity in the framework**, the whole IIT layer is a reparametrisation
of "20", and exactness is automatic for any terminating decimal. The lead's
"needs no fudge term where 6/π² needs 36%" compared a rational-hitting integer
family against an irrational constant. It was not a comparison of evidential
quality, and it was the sentence used to argue the route beat the book's
account.

**One claim was understated.** `h(H₃) = 10` is genuinely **derived**:
`PF/H3CoxeterDiagramDerivation.lean:519` proves
`orderOf H3_coxeterElement = H3_Coxeter_number` from mathlib's
`CoxeterMatrix.H₃` via the Gram matrix, with exponents `{1,5,9}` from the
characteristic polynomial. So the asymmetry is sharp, not symmetric: **the 10
has a derivation chain; the 20 has `norm_num` on a back-solved number.**

## What survives — on the other side of the framework

`PF/IBMPeaksGaloisPair.lean:89`

```lean
theorem NP_fibre_squared : (4 * alpha_NP - 3) ^ 2 = 20
```

Exact, kernel-proved, and **0.95-free**: `4(φ + 1/4) − 3 = 2(2φ − 1) = 2√5`, so
`20 = 4·5 = 4·disc ℚ(√5)`. Verified at 30 dps. It is the completed-square
constant of ch.21's own self-adjointness quadratic, with
`disc = 1280 = 16²·5`. It inherits α_NP's open provenance — `r122 §6` proves
α_NP is independent of every non-definitional postulate — but it does not come
from 0.95. **The circle is breakable from the α-skeleton side, not the
icosahedral side this lead chose.**

Three further 0.95-free factorisations of 20 exist (`10·α_YM`, the polylog
`2·10`, the α_QG multiplier), and 400 appears 0.95-free as `λ₀(YM)² = π²/400`.

## What a real attempt would require

1. **Direction**: diagram → parabolic index → saturation gap, never the reverse.
   It may not cite `low_rank_bound_at_sigma_c`. Drop the IIT/400 layer entirely.
2. **Selectivity** — the real bar. The canonical description of 20 is
   `[W(H₃) : W_{A₂}] = 120/6`, the index of the maximal parabolic stabilising a
   triangular face. The other two maximal parabolics give **12** and **30**. The
   theorem must say why A₂ is forced, and must be *unable* to output 12, 15,
   24, 30 or 60 — all available, each fitting a plausible threshold to within
   0.0167.
3. **Falsifiability**: it must predict one number besides 0.95 from the same
   structure.

## Collateral findings, logged for separate repair

* **`MinimalRigidityForcesLambdaEffExponentProduct.lean` forces nothing.** Its
  six hypotheses are all underscore-prefixed — Lean's marker for unused — and
  the proof term is the unconditional global numeral identity. Provable with the
  rigidity set deleted. Its own docstring concedes "the parametric lift of the
  global-constant identity." The discriminating control: the IIT-Φ-threshold
  file binds and consumes its hypotheses without underscores.
* **The IIT bridge carries two incompatible conventions**, differing by exactly
  2: `8.644` bits in Lean against `4.32` bits at `ch31:182`, where only the
  un-doubled form lands in the cited 4–6 bit band. Repaired in the manuscript
  on 2026-11-02.
* **`Ch2PhiBridgeContinuousSchmidt`** is `∀ μ, nonneg → True` — a vacuous named
  placeholder.
* **An impossibility overclaim**: `codex/SUBSTRATE_FORCES_WHAT_2026-07-26.md:219-220`
  says the 5-fold icosahedral structure *"cannot live inside the substrate
  K-theoretically"*, inferring it from `not_memZ13_one_fifth` (no trace-1/5
  projection, hence no unital `M₅(ℂ) ↪ T∞`). That does not follow: icosahedral
  symmetry needs a 3-dimensional representation, which exists. The
  impossibility-vs-absence pattern.
* **13 routes to 0.95 adjudicated, zero exact**: 4 circular by construction or
  definition, 2 circular by docstring, 1 fitted to an interval of width 2/27
  that does not distinguish 19/20, 4 refuted, 1 withdrawn, 1 unreplicated
  empirical claim about a different observable, 1 sufficient-only theorem.
  `ε_quantum` is defined exactly once, as `σ_c − 6/π²`.

## The one honest next action — DONE 2026-11-02

The strongest statement available here is **negative, and it is one theorem away
from being machine-checked**: formalise that the ternary tower's distinguishable
thresholds are exactly `ℤ[1/3] ∩ [0,1]`, and that `19/20 ∉` that set. It needs
only the `not_memZ13_*` lemmas the corpus already holds. It converts
`ch06:679`'s and `ch07:817`'s prose — *"20 is not a ternary number"* — into a
kernel fact, and permanently closes "0.95 is forced by the substrate" in both
directions. No downgrade is involved: `ch06:464` already files 0.95 as
EMPIRICAL HYPOTHESIS — UNTESTED.

---

## Resolution — `PF/Ch2ThresholdZ13Exclusion.lean`, gated

Written and gated the same day the lead closed. **Gate (Legion verification
tree, never `lake` on Acer):** `lake` exit 0, 3 264 jobs, 16 declarations, zero
`sorryAx`, zero errors, zero warnings in the file, all 16 at
`[propext, Classical.choice, Quot.sound]`, zero project axioms.

**What the corpus actually had.** `Ch2ThresholdSelection.lean:326`
`nineteen_twentieths_not_a_tower_value` proves four `norm_num` disequalities —
`19/20 ≠ 2/3, 8/9, 26/27, 80/81`. Its own docstring, plus `ch06:603`,
`ch06:679` and `ch07:817`, all assert the far stronger *"20 is not a ternary
number."* Four disequalities exclude four values and settle nothing about a
fifth, let alone about every level. The prose was right and the citation
over-attributed. A 14-naming sweep across all 9 490 `PF/*.lean` sources
confirmed `MemZ13` occurred in exactly five files, all α-skeleton, none
mentioning `19/20`.

**What is now proved.**

| theorem | content |
|---|---|
| `not_memZ13_of_prime_den` | the general engine: any prime `p ∤ 3` in the denominator excludes the value |
| `not_memZ13_nineteen_twentieths` | `19/20 ∉ ℤ[1/3]`, by **two** independent proofs (parity; the engine at `p = 5`) |
| `not_memZ13_one_half` | `1/2 ∉ ℤ[1/3]` — the "no unital qubit in the substrate" claim asserted at `SUBSTRATE_FORCES_WHAT_2026-07-26.md:216` and never formalized |
| `nineteen_twentieths_not_any_tower_value` | `19/20 ≠ 1 − 3^{−k}` for **every** `k` |
| `nineteen_twentieths_not_a_level_trace` | the normalized trace of no level projection, at any level |
| `nineteen_twentieths_level_separation` | **`|19/20 − m/3^k| ≥ 1/(20·3^k)`** for every `k` and every integer `m` |
| `separation_constant_is_optimal` | the constant `20` cannot be improved — attained at `k = 0` and `k = 4` |
| `tower_approximates_nineteen_twentieths` | **and yet `ℤ[1/3]` is dense at `19/20`** |

The engine also subsumes the corpus's existing `not_memZ13_three_halves` and
`not_memZ13_one_fifth`, recorded as `three_halves_via_engine` and
`one_fifth_via_engine` — subsumption shown, nothing replaced or deleted.

**Three negative controls, all rejected.** Claiming `26/27` (a real tower
value) is excluded → rejected. Tightening the separation constant `20 → 19` →
rejected. Falsifying the optimality witness `1/20 → 2/20` → rejected. The
pristine module then rebuilt green at identical md5. A green build alone would
have proved nothing.

**Arithmetic independently verified in exact rationals**, 15/15 claims, every
verdict computed from a residual rather than printed as a pre-written label —
including the mod-4 cycle `[1, 3, 9, 7]` of `min |19·3^k − 20m|`, which is why
the bound is attained exactly when `k ≡ 0 (mod 4)`.

**Both directions, deliberately.** The density theorem sits in the capstone
beside the exclusion because the one-directional reading would be a fresh
instance of the overclaim this very file logged at
`SUBSTRATE_FORCES_WHAT_2026-07-26.md:219-220`, where `not_memZ13_one_fifth` was
stretched into *"the 5-fold icosahedral structure cannot live inside the
substrate K-theoretically"* — which does not follow, icosahedral symmetry
needing a 3-dimensional representation that exists.

**Net result.** The ternary tower **neither forces `0.95` nor forbids it.**
`0.95` is simply not one of the tower's values, at a measured and optimal
distance from every one of them, and reachable only in the limit. This closes
*"0.95 is forced by the substrate"* in both directions, which is what the lead
set out to settle — from the arithmetic side, not the icosahedral side it
originally proposed.

No framework constant enters any proof. No `σ_c`, no `Phi_threshold`, no
`low_rank_bound_at_sigma_c`. The only inputs are `19/20` and the powers of `3`.

**Nothing is downgraded.** One prose assertion became a theorem. `ch06:464`
already filed `0.95` as EMPIRICAL HYPOTHESIS — UNTESTED, and `ch06`'s *Settled,
2026-10-05* remark had already withdrawn *"0.95 is not a free parameter"*; both
stand, now on a stronger footing.

### Landed

* `PF/Ch2ThresholdZ13Exclusion.lean` — new, 16 declarations.
* `PF.lean` — registered beside `PF.Ch2ThresholdSelection`. Imports 1 235 →
  1 236, every pre-existing import verified intact. `PF.lean:960` records that
  the file this module imports *"was previously imported by nothing, so `lake
  build` never re-verified it"*; leaving this one unregistered would have
  repeated a defect the manifest itself documents.
* `chapters/ch06_consciousness.tex` — the over-attributing citation at `:603`
  corrected and `:679` cross-referenced, both notes carrying the density
  counterweight. Book gate on Legion.

### Two items left standing, reported not acted on

1. **`ch07:817` carries the same prose** and `ch07_constants.tex` is
   AUTHOR-RESERVED (`INSTRUCTIONS` §2). Read, not touched. It needs the same
   one-line citation correction `ch06:603` received.
2. **`PF.lean:1393`'s manifest comment for `Ch2ThresholdSelection` is stale.**
   It still cites `wedge_square_sign_indefinite`,
   `normalizer_unbounded_in_rank`, `threshold_iff_dimension`,
   `threshold_first_crossed_at_level_three`, `tower_level_values` and
   `levels_two_and_three_straddle`, and still asserts *"the quotient is
   identically 0"* — all of which that file's own §0 withdrew or renamed in its
   rev 2. The comment describes the superseded first attempt.

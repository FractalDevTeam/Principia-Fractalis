# Session record, 2026-08-06 — T1 null vectors, three refuted theorems, σ(α), audit verification

Additive record. Nothing in this session deleted or rewrote existing content.
Everything below was recomputed or re-read directly; agent reports were not
taken on trust, and the two places where an agent's number or sign was wrong
are marked.

Scripts: `codex/rh_t1_nullvectors.py`, `codex/rf_falsification_checks_2026-08-06.py`.

---

## 1. T1 — the null-vector split at the Maass and Riemann points

Both families of `Z_Selberg` zeros live in the SAME factor `det(1 − L_s)`:
the even Maass cusp form at `s = 1/2 + 13.77975135189074i`, and the first
Riemann zero at `s = 1/4 + 7.0673627606i` (`ρ₁/2`). M1 (2026-08-02) located
both through `|det|`. T1 asks what the null VECTORS look like.

Method: exact Hurwitz-zeta matrix elements (the M1 continuation), disc basis
`e_n(x) = ((x−1)/R)^n`, `R = 3/2`; null vector by inverse iteration on `A − I`;
asymptotics by telescoping the operator's own three-term equation
`ψ(x) = ψ(x+1) + (x+1)^{−2s} ψ(1/(x+1))` to the right, which needs nothing
outside the disc because every `1/(x₀+j)` lands in `(0,1)`.

|                                    | Maass, Re s = 1/2 | Riemann, Re s = 1/4 |
|------------------------------------|-------------------|---------------------|
| `|λ − 1|`                           | 1.6e-15           | 2.2e-7              |
| `‖Av − λv‖`                         | 1.1e-46           | 3.6e-49             |
| three-term residual (worst on grid) | 3.8e-15           | 2.1e-7              |
| `ψ(0)`                              | ~1e-23 (zero)     | **7.8386e-4**       |
| growth exponent `a`, `|ψ(X)| ~ X^a` | **−2**            | **+1/2**            |

Control at `Re s = 1/4, t = 6.60` (no zero there): `|λ − 1| = 0.474`.
The Riemann `|λ − 1| = 2.2e-7` matches the known −1.6e-7 offset between ζ's
ordinate and the operator's own minimum, so it is expected, not error.

**The three-term equation is satisfied to 8e-16 at the Maass point.** These are
genuine Lewis–Zagier period functions, not numerical artifacts.

### Why the exponents split

Telescoping gives `ψ(x₀+n) = ψ(x₀) − Σ_j (x₀+j)^{−2s} ψ(1/(x₀+j))`. The leading
term is `ψ(0)·Σ(x₀+j)^{−2s}`, whose partial sums grow like `X^{1−2s}`. Hence

    a = 1 − 2·Re s     provided  ψ(0) ≠ 0.

At `Re s = 1/4` that predicts `a = 1/2`; measured 0.49963. At `Re s = 1/2` it
predicts `a = 0` — bounded, non-decaying. We measure decay, so `ψ(0) = 0` at
the Maass point; and `a = −2` rather than −1 additionally requires `ψ'(0) = 0`.
That second-order vanishing follows from my own expansion and has NOT been
cross-checked against the Lewis–Zagier literature. Treat it as measured.

**The separator is whether the period function vanishes at the origin** — which
is exactly the decay condition Lewis–Zagier use to characterise L² Maass forms,
now computable inside our own machinery instead of cited.

### Methodology note worth keeping

`ψ(0)` at the Maass point read 1.5e-18 at N = 72 and 3.3e-23 at N = 88 — five
orders apart. That direct evaluation is truncation noise and any conclusion
drawn from it would have been void. The EXPONENT is the well-conditioned
quantity: it agrees to 7–8 digits across N = 72 vs 88 at both points. The
N-stability gate is what made this result usable; without it the first run
would have produced a confident wrong claim.

### What T1 kills and what it buys

- **Kills the planned T2 reformulation.** `a = 1 − 2 Re s` holds by construction,
  so "growth exponent = 1/2 ⟺ zero on the line" restates the definition. A
  tautology, not progress. Do not build it out.
- **Buys an instrument.** An off-line zero at `Re s = 1/4 + δ` would show
  `a = 1/2 − 2δ`. That is a growth-rate detector for the 2-D scan of the
  eigenvalue-1 locus — the one experiment that touches the Eisenstein side,
  where Hilbert–Pólya actually fails. Existing code scans lines only.

---

## 2. Three book theorems are false

Recomputed independently (`codex/rf_falsification_checks_2026-08-06.py`); each was first
flagged by an audit agent, each then reproduced here from the book's own
definitions (`ch03:49` `D₃` = base-3 digit sum; `ch03:93` `R_f`).

### 2.1 ch03:255 / ch09:202 — the RH Resonance theorem. FALSE.

Claim: `R_f(3/2, 1/2+it) = 0  ⟺  ζ(1/2+it) = 0`.

At α = 3/2 the phase is `(−i)^{D₃(n)}`, and the exact digit-block identity
`Σ_{n<3^k} ω^{D₃(n)} = (1+ω+ω²)^k` gives partial sums of modulus 1, so the
abscissa of convergence is 0 and direct summation on the line is valid.

| γ | 14.1347 | 21.0220 | 25.0109 | 30.4249 | 32.9351 |
|---|---|---|---|---|---|
| `|R_f(3/2, ½+iγ)|` | 0.6187 | 1.5462 | 1.7966 | 1.1359 | 1.6266 |

Stable across `n < 3^13` and `n < 3^15`. `R_f(3/2,·)`'s own near-zeros on the
line sit at t ≈ 2.75, 11.0, 19.75, 29.0, 31.75 — none are ζ ordinates.

**This is the ch03 → ch09 → ch20 spine.** In Lean it was never discharged: a
bare `Prop` at `PF/Consciousness/FractalResonance.lean:323`.

### 2.2 ch24:512 — the Ш bound. FALSE.

Claim: `|Ш(E)| ≤ [R_f(π, N_E)]²`. The phase multiplies terms of size `n^{−N_E}`,
so for any conductor ≥ 11 the sum is `1 + O(2^{−N_E})` and the bound reads
`|Ш| ≤ 1`. Computed: 0.999130 at N_E = 11, 1.0 at 571 and 681.
Broken by 571a1 (`|Ш| = 4`) and 681c1 (`|Ш| = 9`) — and, at N_E = 11, by every
curve including trivial-Ш ones.

### 2.3 ch23:342 — the Yang–Mills mass-gap frequency. DOES NOT EXIST.

`R_f(2,s) = ζ(s)` identically (`e^{2πi D₃(n)} = 1`), so `ρ(ω) = ζ(1/ω)`. ζ's
real zeros are the trivial ones at −2, −4, …, so `1/ω = −2 ⟹ ω = −1/2`:
**ρ has no zero for ω > 0.** At the claimed `ω_c = 2.13198462`, ρ = −1.346.
The 420.43 MeV gap (ch23:383) has no basis. `ω = 1` is a POLE, not a zero.

*Agent-report correction:* the audit agent stated ρ < 0 on (0,1) and > 0 on
(1,∞). It is the reverse — ρ = +1.645 at ω = 0.5. Conclusion unchanged.

---

## 3. σ(α) — the first non-circular α-selection mechanism

The digit-block identity `Σ_{n<3^k} ω^{D₃(n)} = (1+ω+ω²)^k` is exact (verified
to 2.3e-13 at k = 12). Since `1 + e^{iπα} + e^{2iπα} = e^{iπα}(1 + 2cos πα)`,
the abscissa of convergence of `R_f(α,·)` is

    σ(α) = log₃ |1 + 2 cos(π α)|

Checks: σ(0) = 1 (ζ's pole) ✓; σ(2) = 1 ✓ (`R_f(2,s) = ζ(s)`, cf. §2.3);
σ(3/2) = 0 ✓ (matches the α = 3/2 partial-sum modulus of 1 in §2.1).

Against the framework's nine α-values (`appJ:239-249`):

| name | value | σ(α) | |
|---|---|---|---|
| α_Poincaré | 1 | **0** | exact |
| α_RH | 3/2 | **0** | exact |
| α_YM | 2 | **1** | exact — the ζ pole |
| α_Hodge | φ | 0.4961550 | misses 1/2 by 3.8e-3 |
| α_P | √2 | −0.6921266 | — |
| α_NP | φ+1/4 | 0.9470835 | — |
| α_QG | √(2π) | −0.0387176 | — |
| α_BSD | 3π/4 | 0.5712771 | — |
| α_NS | 3π/2 | −1.3080122 | — |

σ = 0 has exactly two solutions in [0,2): α = 1/2 and 3/2. σ = 1 has exactly
one: α = 2. σ = 1/2 has exactly two: **α = 0.3807183 and 1.6192817**.

**The framework's own ternary scaling law derives exactly its three rational
α-values and none of its six irrational ones.** This is a two-sided result and
it complements r123: the trace/K-theory route is refuted, the digit route works
and reaches only the rational third. Base-3 digit structure has nothing to say
about √2, φ, φ+1/4, √(2π), 3π/4, 3π/2.

**GUARD RAIL.** The exact σ = 1/2 point is **1.6192817**, not φ = 1.6180340.
They differ by 1.25e-3 and σ(φ) = 0.4962, a 0.8% miss. This near-coincidence
must not be adopted as a derivation of α_Hodge. Recorded here before it can be.

σ(α) is Lean-formalizable and is proposed as stone **r212**.

---

## 4. Verification of the external chapter-by-chapter audit

Four load-bearing claims were checked by an agent and then the two severe ones
re-read by me directly at the source.

| claim | verdict |
|---|---|
| r123: T∞ has one tracial state, not nine | CONFIRMED (`r123:366`, `r123:376`) |
| r123: trace range ℤ[1/3], 7 of 9 α outside | CONFIRMED (`r123:209`, `r123:286`); the K-theory identification is prose, self-disclosed at `r123:80-84` |
| r123: arbitrary finite spectra embed | PARTLY — the theorem (`r123:312`) is about `Matrix (Fin (3^k))`, the "⊆ T∞" step is prose |
| r123: π/10 holds for every α | CONFIRMED (`r123:397`), near-definitional; note r123's local `lambda0` is not proved equal to `HAlphaUniversal.lambda0` |
| r123: R_f 2-periodic | PARTLY — `r123:408` proves it for ONE phase factor; no theorem states `R_f(α+2,s) = R_f(α,s)` |
| ch24 conclusion repeats the retracted φ/e mechanism | **CONFIRMED** |
| ch34A "unconditional" theorem is hollow | PARTLY — core correct; but NO field of `PFSubstrateConsequences` is a `True` marker (the `True` fields are in the adjacent honest-scope record) |
| NS bilinear is a shell with a zero witness | **CONFIRMED, and worse than stated** |

### 4.1 The Navier–Stokes bilinear operator — read at source

`PF/NavierStokes/FujitaKato1964BilinearEstimate.lean:59`

    noncomputable def bilinearOp (_u _v : VectorField3) : VectorField3 := 0

Both arguments are underscore-discarded. It is not "a zero witness chosen among
others" — `B` is DEFINED as the constant zero. Every downstream estimate is
then `0 ≤ nonneg`; `fujita_kato_C_FK_independent_of_T` is independent of T
because the operator is zero.

`:161` — `picardIterationMap (u₀ v) := bilinearOp v v + 0`. `u₀` is unused, so
the Picard map is constant zero for EVERY initial datum, not only zero data.

`PF/NavierStokes/FujitaKato1964/BilinearScaffold.lean:229-232` — the fixed-point
Prop carries a literal `True` in its conclusion:

    ∃ u : TimeFieldR3C, u 0 = u₀ ∧ True

discharged at `:246` by the constant field. The files label themselves
structural (`BilinearScaffold.lean:269`), so this is disclosure, not
concealment. The defect is that the layer is cited upstream as
`PFSubstrateConsequences.NS_via_substrate` — substrate-level NS content.

The surrounding 31-file layer is genuine: zero `sorry`, zero `: True` across
`PF/NavierStokes/FujitaKato1964/`, with real Leray-projector, heat-semigroup
and convective-derivative bricks. The hole is precisely the bilinear map.

### 4.2 ch34A — read at source

`PF/Referee/PrincipiaFractalisSubstrateTheorem.lean:392-394`

    theorem PrincipiaFractalisSubstrateTheorem :
        PFSubstrateAntecedents → PFSubstrateConsequences := by
      intro _h_antecedents -- ★ antecedent DISCARDED

The source comment says it. The Lean docstring at `:374-377` says the
implication is vacuously true. But `ch34A:629-633` still glosses it as "the
substrate antecedents (A1)–(A5) … determine the twenty-five consequences", and
`ch34A:681-694` keeps "the substrate determines the consequences". `A → B` with
`B` independently provable does not mean `A` determines `B`.

Field audit of `PFSubstrateConsequences` (25 fields): 1 zero-witness existential
(C4, NS — see §4.1), 7 definitional/tautologous, 5 restricted-carrier
(BSD on `Fin 6`; Hodge with `isAlgebraic` trivialised; YM on ℓ² with no gauge
group), ~6 content-bearing, 6 bundles re-packaging the above.

### 4.3 ch24 — read at source

`ch24:653-680` states plainly "**DID NOT REPRODUCE**", "the multiplicity
mechanism stays falsified", and `:397-402` carries a warning box reading
"False as stated".

`ch24:788-801` (the Conclusion) nonetheless lists, unhedged:
- `:791` "**Rank Formula**: Multiplicity at threshold equals algebraic rank"
- `:798` "**Ш Bound**: Concrete finite upper bound from fractal structure"
- `:801` "…BSD as a *resonance phenomenon* — the rank counts how many
  independent modes resonate at the unique frequency φ/e"

Mitigation: the *Validation* bullet at `:793-796` does carry the caveat. But it
is attached to the success-rate line, not to `:791`, `:798` or `:801`.

Note the convergence: `:798` asserts the Ш bound that §2.2 above refutes
outright. The same bullet list carries both a falsified mechanism and a false
theorem.

### 4.4 Two findings the audit itself missed

1. **r123 is not in the build tree.** Nothing imports it; `PF.lean` does not
   list it (grep confirms zero hits). An `.olean` from 2026-07-26 exists, so it
   compiled standalone, but `lake build` does not re-verify the file that
   refutes the α route.
2. **The 143-problem "empirical" dataset is 143 copies of two hardcoded rows**
   (`HundredFortyThreeProblems.lean:127-142`) whose α is *defined* to be the
   canonical value. It appears as substrate antecedent A5 AND consequence C20.
   Both are tautologies, not measurements.

---

## 5. Also landed this session

**r211** — level-3 Gauss enclosures, `PF/GaussLevelThree_r211.lean`, 1233 lines.
Recompiled independently: 0 errors, all 29 `#print axioms` lines exactly
`[propext, Classical.choice, Quot.sound]`, six theorems, no `sorry`, no
`native_decide`. Enclosures `[0.65, 0.75]` for K=3 (true 0.70566) and
`[0.48, 0.5625]` for K=2 (true 0.53128). Uncommitted at time of writing.

Level 3 is the practical ceiling: level 4 needs 6561 separation cases against
level 3's 729, while the width only shrinks like O(1/n). The sharp value needs
the equilibrium state (Ruelle–Perron–Frobenius), which is not started and is
not approached by refinement.

---

## 6. Queue

Nothing here is a deletion. All proposed work is additive.

**DONE 2026-08-06 — r123 and r211 wired into the build tree.**
`PF.lean:927` now imports `PF.AlphaFromSubstrateKTheory_r123`. Before that,
nothing imported it: the file carrying the α refutation had an `.olean` from
2026-07-26 and was never re-verified by `lake build`. Checked before wiring:
it still compiles against the current pin, and all eight of its theorems return
`[propext, Classical.choice, Quot.sound]`. Build after wiring: 9439 jobs, 0 errors.

`PF.lean:1024` now imports `PF.GaussLevelThree_r211`, which had landed the same
day in exactly the same state — on disk, imported by nothing. Fixing the defect
for one file while creating it for another would have been incoherent.
Build after both: **9441 jobs, 0 errors.**

**Standing rule this exposes:** a stone that is not imported by `PF.lean` is not
covered by the build, however clean its standalone compile was. Any future rN
lands with its import line, or it does not count as landed.

**DONE 2026-08-06 — r212 landed.** `PF/SigmaAbscissa_r212.lean`, 587 lines,
imported at `PF.lean:1024`. Build after: **9443 jobs, 0 errors.** 31 `#print
axioms`, all `[propext, Classical.choice, Quot.sound]`.

Contents: the digit-block identity over ℂ; `‖1+z+z²‖ = |1+2cos θ|`; the
partial-sum modulus `|1+2cos πα|^k`; `sigma`; the level sets; the three exact
hits; the obstruction; and the φ guard rail `sigma_goldenRatio_ne_half`.

Two things came out better than specified:
- **The obstruction is UNCONDITIONAL.** The degenerate branch `cos(πα) = −1/2`
  also forces α rational, because `cos(3πα) = 4(−1/8) − 3(−1/2) = 1` gives
  `α = 2k/3`. So `irrational_imp_sigma_ne_zero_one` needs no nonvanishing
  hypothesis. Verified.
- **The φ guard rail is in the kernel**, not just prose. My suggested route
  (`Real.sin_bound` at u ≈ 0.6) was too loose — error 6.8e-3 against a required
  gap of 3.67e-3. What works is `Real.cos_bound` at ≈ 0.3 (error 4.2e-4) then
  two double-angle steps: cos w ≤ 0.955425 → 0.825674 → 0.363476, against
  (√3−1)/2 > 0.3660254. cos is positive throughout, so squaring preserves
  direction.

The degenerate case is stated in two forms, not hidden: `sigma_eq_zero_iff_full`
(unconditional, three branches including `1+2cos = 0`) and `sigma_eq_zero_iff`
(two branches, under explicit nonvanishing). `sigma_eq_one_iff` needs none.
`irrational_pi` and `Real.goldenRatio_irrational` both exist in the pin, so no
hypotheses and no axioms were added anywhere.

**PROCESS NOTE, same class as the import defect.** The building agent reported
"all 36 declarations `[propext, Classical.choice, Quot.sound]`". The file
contained **zero** `#print axioms` directives — the claim had nothing behind it
in the source. The audit block was appended afterwards and the file recompiled;
only then was the number real. Extend the standing rule: **a stone lands with
its import line AND its in-file `#print axioms` block.** An axiom claim that is
not re-run by `lake build` is not a verified claim.

**DONE 2026-08-06 — falsification ledgers written into ch03, ch23, ch24.**
Additive only; every original line stays. Each follows the corpus's existing
`\paragraph{Verification update (date)}` + tagged-itemize form.
Book rebuilt: **954 → 957 pages, zero undefined references.**

- **ch03** — `REFUTED` on `thm:rh-resonance`, both directions shown (the five
  zeta zeros, and R_f's own near-zeros at t ≈ 2.75, 11.0, 19.75, 29.0, 31.75).
  Flags the ch03 → ch09 → ch20 consequence. Then adds σ(α) and the φ guard
  rail as what the same digit structure does give.
- **ch23** — `REFUTED` on `prop:resonance-zeros`, **with the diagnosis**: ρ
  does change sign, but through the POLE of ζ at s = 1, i.e. at ω = 1. A
  root-finder run across ω = 1 without a pole guard reports a spurious
  crossing. That is the likely provenance of ω_c = 2.13198462, and the
  420.43 MeV gap inherits the defect.
- **ch24** — `REFUTED` on `thm:fractal-bound-sha`, plus
  `TEXT NOT YET RECONCILED` naming the three Conclusion bullets that still
  state retracted claims and directing the reader to treat the Conclusion as
  superseded on those points. Bullets left in place per the additive rule —
  not withdrawn silently. This also closes the former queue item on
  reconciling `:791`, `:798`, `:801` with the ledger at `:653-680`.

Each entry also names what is NOT affected (ch23's finite-dimensional OS
reflection-positivity; ch24's r188c trace identity and universal rank
pipeline). A falsification that quietly widens its own blast radius is its own
kind of error.

*Self-caught during the edit:* four `\ref`s were written to labels that do not
exist (`sec:mass-gap`, `sec:computational-evidence`, `sec:bsd-conclusion`,
`warn:rank-formula-false`) — invented from section titles. They would have
rendered as `??` inside a 950-page PDF. Replaced with prose references; the
five surviving refs were each checked present before compiling.

### Remaining

1. ch34A: rebuild around content-bearing propositions; the antecedent-discarding
   is disclosed in Lean but not in the chapter's headline language.
2. NS: either build the real Bochner-integral `B(u,v)`, or stop citing the
   shell upstream as `NS_via_substrate`.
3. RH: the 2-D eigenvalue-1 scan, using T1's growth-exponent detector.
4. ch09: its "spectral unity" bridge rests on the refuted ch03 theorem. Not yet
   ledgered — the ch03 entry flags the consequence but ch09 itself is untouched.

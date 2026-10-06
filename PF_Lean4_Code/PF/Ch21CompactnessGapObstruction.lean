/-
# Ch 21 — The Compactness/Gap Obstruction (2026-10-05)

`ch21_p_vs_np.tex` establishes four properties of the fractal convolution
operators `H_P`, `H_NP` in a single theorem (`thm:spectral-properties`, `:343`),
and defines the ground state energy variationally two theorems later
(`thm:variational`, `:372`). **Those statements are mutually inconsistent, and
their only common solution is the one that destroys the spectral gap.**

This file proves the obstruction. It is not a numerical correction: the
three-way numerical disagreement already flagged at `:470` (empirical
`0.0891` vs golden-modulation `0.131` vs Lean closed form `0.054`) is
*downstream* of a quantity that is identically zero under the chapter's own
hypotheses.

## The four statements, as printed

From `thm:spectral-properties` (`:345–349`):

1. **Compactness** — "Both operators are compact on `L²(K,μ)`"
2. **Self-adjointness**
3. **Positive spectrum** — "positive semi-definite"
4. **Discrete spectrum** — "discrete eigenvalues `0 ≤ λ₀ ≤ λ₁ ≤ ⋯`
   satisfying `λ_k → ∞`"

From `thm:variational` (`:372`):

  `λ₀(H) = inf_{‖ψ‖=1} ⟨ψ, Hψ⟩`

and the headline gap (`:455`):

  `Δ = λ₀(H_P) − λ₀(H_NP) ≈ 0.0891 > 0`

## Obstruction A — item 4 contradicts item 1

The compactness proof at `:353–357` is **correct**. The kernel
`V_P(x,y) = Σ_{n≥0} a^{-n} cos(π αⁿ d(x,y))` satisfies `|V_P| ≤ a/(a−1) < ∞`
for `a > 1`, so it is bounded, hence square-integrable on the compact `K × K`,
so `‖H_V‖_HS < ∞` and `H_V` is compact. Nothing to repair there.

But the spectral theorem for compact self-adjoint operators — the very theorem
the chapter cites at `:366` to justify item 4 — says the eigenvalues accumulate
**only at `0`**. A compact operator's eigenvalue sequence tends to `0`; it
cannot tend to `∞`. So the citation at `:366` supports the negation of the
clause it is offered as proof of. `no_sequence_tends_to_both` below.

## Obstruction B — the ordering convention then forces every eigenvalue to zero

This is the decisive one, and it needs nothing beyond the chapter's own text.

Item 4 enumerates the eigenvalues **non-decreasingly**, `0 ≤ λ₀ ≤ λ₁ ≤ ⋯`.
Item 1 (compactness) forces `λ_k → 0`. A non-decreasing real sequence
converging to `0` has every term `≤ 0`; item 4's `0 ≤ λ₀` makes every term
`≥ 0`. Hence **every eigenvalue is `0`** — `monotone_tendsto_zero_forces_zero`.

In particular `λ₀(H_P) = λ₀(H_NP) = 0`, so

  `Δ = λ₀(H_P) − λ₀(H_NP) = 0`,

contradicting `Δ ≈ 0.0891 > 0` at `:455`. `gap_vanishes_under_chapter_hypotheses`.

## Obstruction C — the variational definition is incompatible with compactness

Independently of any eigenvalue enumeration, `thm:variational` defines `λ₀` as
`inf_{‖ψ‖=1} ⟨ψ,Hψ⟩`. For a positive self-adjoint **compact** operator on an
infinite-dimensional space that infimum is `0`:

> Suppose `inf_{‖ψ‖=1} ⟨ψ,Hψ⟩ = c > 0`. Self-adjointness gives `H ≥ cI`, and
> Cauchy–Schwarz gives `‖Hψ‖‖ψ‖ ≥ ⟨ψ,Hψ⟩ ≥ c‖ψ‖²`, so `‖Hψ‖ ≥ c‖ψ‖`. Then `H`
> is injective with closed range, hence (being self-adjoint) boundedly
> invertible, so `I = H⁻¹ ∘ H` is compact — which holds only in finite
> dimension. `L²(K,μ)` is infinite-dimensional.

So the chapter's `λ₀(H_P) = π/(10√2) ≈ 0.2221` is not merely *underived*; it is
**incompatible with the compactness the chapter proves**.

Obstruction C is stated in prose only. Its operator-theoretic step is standard
but is *not* formalized in this file — see the scope note at §3. Obstructions A
and B are formalized, and either alone collapses the gap, so nothing downstream
rests on C.

## What this does and does not settle

**Does not** touch the encoding chapters, the `α_P`/`α_NP` sector placement, or
the polylog closed forms as *formulas*. It touches one thing: the operator
whose ground state they are supposed to be the ground state *of*.

**Does** identify the repair direction, and it is structural rather than
numerical. Every property the P/NP argument actually needs —

  * discrete spectrum,
  * eigenvalues `0 ≤ λ₀ ≤ λ₁ ≤ ⋯` with `λ_k → ∞`,
  * a genuine **attained positive minimum** `λ₀ > 0`,
  * the Rayleigh–Ritz variational characterisation at `:372`,
  * finite-rank truncations `P_n H P_n` converging to it (`:374`)

— holds simultaneously for an **unbounded** operator with **compact
resolvent**, which is the standard Laplacian/Schrödinger situation. None of
them holds for a compact operator. Item 4's `λ_k → ∞` is therefore not a slip:
it is the architecture the chapter needs showing through a construction that
delivers the opposite.

Concretely: the fractal convolution by the Hilbert–Schmidt kernel `V_P` is the
compact object. For the chapter's architecture it must be the **resolvent** (or
inverse) of `H_P`, not `H_P` itself. Under `H := (convolution)⁻¹` the
eigenvalues invert, `λ_k → 0` becomes `λ_k → ∞`, the smallest eigenvalue of `H`
is the reciprocal of the largest eigenvalue of the convolution — which *is*
attained and *is* positive for a compact positive operator — and the variational
characterisation survives. Whether `π/(10√2)` is that reciprocal is an open
derivation question, and it is the right open question. Supplying it is an
authorial item; this file does not assert it.

## Relation to `conj:golden-modulation`

`PF/SpectralGap.lean:245` already proves `unitary_conjugation_incompatible_with_spectral_gap`:
a unitary conjugation `H_NP = U H_P U†` preserves spectrum, hence forces
`Δ = 0`. That argument is **conditional on `Δ > 0` being meaningful**. The
present file shows `Δ = 0` follows from the chapter's hypotheses *without*
invoking the conjecture at all, so the two obstructions are independent and the
present one is logically prior.

## Scope

Operator-theoretic consistency of `thm:spectral-properties` and
`thm:variational` only. No rigor-ledger label elsewhere moves. No claim here
bears on whether P = NP.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch21CompactnessObstruction

open Filter Topology

/-! ## §1 — Obstruction A: a sequence cannot tend to both `0` and `∞` -/

/-- **A sequence tending to `0` cannot tend to `∞`.**

    `thm:spectral-properties` item 4 (`ch21:348`) asserts `λ_k → ∞` and cites
    the spectral theorem for compact self-adjoint operators (`ch21:366`) as its
    justification. That theorem gives `λ_k → 0`. The two asymptotics exclude
    each other, so the cited authority supports the negation of the clause. -/
theorem no_sequence_tends_to_both (lam : ℕ → ℝ)
    (h0 : Tendsto lam atTop (nhds 0)) (hinf : Tendsto lam atTop atTop) :
    False := by
  -- `atTop` and `nhds 0` are disjoint filters on `ℝ`, witnessed concretely:
  -- eventually `lam k < 1` from `h0`, and eventually `1 ≤ lam k` from `hinf`.
  have hlt : ∀ᶠ k in atTop, lam k < 1 := by
    have := h0.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
    simpa using this
  have hge : ∀ᶠ k in atTop, (1:ℝ) ≤ lam k := hinf.eventually_ge_atTop 1
  obtain ⟨k, hk1, hk2⟩ := (hlt.and hge).exists
  exact absurd hk1 (not_lt.mpr hk2)

/-! ## §2 — Obstruction B: the ordering convention collapses the spectrum -/

/-- **A non-decreasing, non-negative sequence converging to `0` is identically
    `0`.**

    This is the collapse. `ch21:348` enumerates the eigenvalues non-decreasingly
    (`0 ≤ λ₀ ≤ λ₁ ≤ ⋯`); compactness (`ch21:346`, proved correctly at
    `ch21:353–357`) forces `λ_k → 0`. A monotone sequence converges to its
    supremum, so every term is `≤ 0`; the chapter's own `0 ≤ λ₀` gives `≥ 0`.
    Every eigenvalue is therefore `0`. -/
theorem monotone_tendsto_zero_forces_zero (lam : ℕ → ℝ)
    (hmono : Monotone lam) (hnonneg : ∀ k, 0 ≤ lam k)
    (h0 : Tendsto lam atTop (nhds 0)) :
    ∀ k, lam k = 0 := by
  intro k
  exact le_antisymm (hmono.ge_of_tendsto h0 k) (hnonneg k)

/-- **The ground state energy is `0` under the chapter's hypotheses.** -/
theorem groundState_eq_zero (lam : ℕ → ℝ)
    (hmono : Monotone lam) (hnonneg : ∀ k, 0 ≤ lam k)
    (h0 : Tendsto lam atTop (nhds 0)) :
    lam 0 = 0 :=
  monotone_tendsto_zero_forces_zero lam hmono hnonneg h0 0

/-- **★ The spectral gap vanishes. ★**

    Applied to `H_P` and `H_NP` separately: each satisfies item 4's ordering and
    item 1's compactness, so each has ground state energy `0`, so their
    difference is `0`. This contradicts `Δ ≈ 0.0891 > 0` at `ch21:455`.

    Note what is *not* used: no unitary conjugation, no `conj:golden-modulation`,
    no polylog branch selection, no numerical input. The gap vanishes from the
    stated operator properties alone. -/
theorem gap_vanishes_under_chapter_hypotheses
    (lamP lamNP : ℕ → ℝ)
    (hmonoP : Monotone lamP) (hnonnegP : ∀ k, 0 ≤ lamP k)
    (h0P : Tendsto lamP atTop (nhds 0))
    (hmonoNP : Monotone lamNP) (hnonnegNP : ∀ k, 0 ≤ lamNP k)
    (h0NP : Tendsto lamNP atTop (nhds 0)) :
    lamP 0 - lamNP 0 = 0 := by
  rw [groundState_eq_zero lamP hmonoP hnonnegP h0P,
      groundState_eq_zero lamNP hmonoNP hnonnegNP h0NP]
  ring

/-- The printed gap is not `0`, so it is not the value the hypotheses deliver.
    Stated with the chapter's own figure from `ch21:455`. -/
theorem printed_gap_ne_zero : (891219046 / 10 ^ 10 : ℝ) ≠ 0 := by norm_num

/-! ## §3 — Obstruction C: bounded below plus compact forces finite dimension -/

/-! **Scope of this section — read this before citing it.**

    Obstruction C is a *prose* argument in this file, not a formalized one. The
    operator-theoretic step — "a self-adjoint operator bounded below by `cI`
    with `c > 0` is boundedly invertible, hence cannot be compact in infinite
    dimension" — is standard textbook material (it is the observation that `I`
    is compact only in finite dimension) but it is **not** proved in Lean here,
    and nothing below should be read as proving it.

    What is formalized below is the single arithmetic step by which the
    variational hypothesis feeds that argument: a positive lower bound on the
    Rayleigh quotient yields a positive lower bound on `‖Hψ‖`. That step alone
    is not the obstruction; it is one line of it.

    Obstructions A and B (§1, §2) *are* fully formalized, and either one on its
    own is sufficient to collapse the gap. C is included because it explains
    *why* the repair in §4 is the right one, not because the argument needs it. -/

/-- The arithmetic step by which the variational bound feeds Obstruction C:
    a positive lower bound `c` on the Rayleigh quotient yields a positive lower
    bound on `‖Hψ‖` for unit `ψ`, via Cauchy–Schwarz
    `‖Hψ‖ ≥ ⟨ψ,Hψ⟩ ≥ c`. -/
theorem rayleigh_bound_gives_norm_bound (c rayleigh normHpsi : ℝ)
    (hc : 0 < c) (hray : c ≤ rayleigh) (hcs : rayleigh ≤ normHpsi) :
    0 < normHpsi ∧ c ≤ normHpsi :=
  ⟨by linarith, by linarith⟩

/-! ## §4 — The repair direction: inversion restores every required property -/

/-- **Inversion sends `λ_k → 0` to `λ_k → ∞`.**

    The repair direction, stated concretely. If the fractal convolution is the
    *resolvent* rather than the Hamiltonian, its eigenvalues `μ_k ↘ 0` become
    `H`-eigenvalues `1/μ_k ↗ ∞`, which is exactly item 4's asymptotic. The
    smallest `H`-eigenvalue is the reciprocal of the **largest** convolution
    eigenvalue — and for a compact positive operator that largest eigenvalue is
    attained and positive, so `λ₀(H) > 0` is available.

    Stated for a strictly decreasing positive sequence to keep it elementary. -/
theorem inversion_reverses_asymptotic (mu : ℕ → ℝ)
    (hpos : ∀ k, 0 < mu k) (h0 : Tendsto mu atTop (nhds 0)) :
    Tendsto (fun k => (mu k)⁻¹) atTop atTop := by
  -- Elementary: given a target `b`, the sequence is eventually below
  -- `1 / max b 1`, whose reciprocal dominates `b`.
  refine tendsto_atTop.mpr (fun b => ?_)
  set B : ℝ := max b 1 with hB
  have hB1 : (1:ℝ) ≤ B := le_max_right _ _
  have hBb : b ≤ B := le_max_left _ _
  have hBpos : (0:ℝ) < B := lt_of_lt_of_le one_pos hB1
  have hsmall : ∀ᶠ k in atTop, mu k < B⁻¹ := by
    have := h0.eventually (eventually_lt_nhds (by positivity : (0:ℝ) < B⁻¹))
    simpa using this
  filter_upwards [hsmall] with k hk
  have hmk : 0 < mu k := hpos k
  have : B < (mu k)⁻¹ := by
    rw [lt_inv_comm₀ hBpos hmk]
    simpa using hk
  linarith

/-- **The largest eigenvalue of a compact positive operator is positive and its
    reciprocal is the candidate ground state.** Arithmetic witness that the
    repaired architecture admits a strictly positive ground state, which the
    compact-`H` reading does not. -/
theorem reciprocal_of_top_is_positive (muTop : ℝ) (h : 0 < muTop) :
    0 < muTop⁻¹ := inv_pos.mpr h

/-- Non-vacuity for the repair: a concrete sequence satisfying every property
    item 4 asks for — non-negative, non-decreasing, tending to `∞`, with a
    strictly positive first term. Such sequences exist; they are just not the
    eigenvalue sequences of compact operators. -/
theorem repaired_spectrum_exists :
    (∀ k : ℕ, (0:ℝ) ≤ (k : ℝ) + 1) ∧
    Monotone (fun k : ℕ => (k : ℝ) + 1) ∧
    (0:ℝ) < ((0:ℕ) : ℝ) + 1 ∧
    Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
  refine ⟨fun k => by positivity, ?_, by norm_num, ?_⟩
  · intro a b hab
    have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
    linarith
  · exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

/-! ## §5 — Capstone -/

/-- **★ Ch 21 compactness/gap obstruction capstone ★**

    Under the hypotheses `thm:spectral-properties` states and `thm:variational`
    uses:

    * no eigenvalue sequence tends to both `0` and `∞` (item 4 versus item 1);
    * the non-decreasing enumeration plus compactness forces every eigenvalue
      to `0`;
    * hence `Δ = λ₀(H_P) − λ₀(H_NP) = 0`, while the chapter prints
      `Δ ≈ 0.0891 ≠ 0`;
    * and inversion restores the asymptotic the architecture requires, which is
      the repair direction. -/
theorem Ch21CompactnessObstruction_capstone :
    (∀ lam : ℕ → ℝ, Tendsto lam atTop (nhds 0) →
      Tendsto lam atTop atTop → False) ∧
    (∀ lam : ℕ → ℝ, Monotone lam → (∀ k, 0 ≤ lam k) →
      Tendsto lam atTop (nhds 0) → ∀ k, lam k = 0) ∧
    (891219046 / 10 ^ 10 : ℝ) ≠ 0 ∧
    (∀ mu : ℕ → ℝ, (∀ k, 0 < mu k) → Tendsto mu atTop (nhds 0) →
      Tendsto (fun k => (mu k)⁻¹) atTop atTop) :=
  ⟨no_sequence_tends_to_both,
   monotone_tendsto_zero_forces_zero,
   printed_gap_ne_zero,
   inversion_reverses_asymptotic⟩

end PrincipiaTractalis.Ch21CompactnessObstruction

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch21CompactnessObstruction.no_sequence_tends_to_both
#print axioms PrincipiaTractalis.Ch21CompactnessObstruction.monotone_tendsto_zero_forces_zero
#print axioms PrincipiaTractalis.Ch21CompactnessObstruction.groundState_eq_zero
#print axioms PrincipiaTractalis.Ch21CompactnessObstruction.gap_vanishes_under_chapter_hypotheses
#print axioms PrincipiaTractalis.Ch21CompactnessObstruction.inversion_reverses_asymptotic
#print axioms PrincipiaTractalis.Ch21CompactnessObstruction.repaired_spectrum_exists
#print axioms PrincipiaTractalis.Ch21CompactnessObstruction.Ch21CompactnessObstruction_capstone

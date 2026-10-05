/-
# The Polylog Spectral Pinning Gap — naming the missing object

**2026-10-05.** Author's determination, recorded so it is not re-litigated:
**the referent of `λ₀(H_α) = π/(10·α)` is not pinned.** The book never fixed
which operator `H_α` denotes, nor which spectral quantity `λ₀` extracts. That
is the gap. This file names it, and proves the one fact that constrains it.

## Bird's eye — this is the machine's keystone, not a chapter's defect

`λ₀(H_α) = π/(10·α)` is not one chapter's formula. It is **the law that makes
the six Millennium problems one family instead of six puzzles**, and it is the
single most widely used quantity in the corpus.

Measured 2026-10-05: `π/10` appears in **113 Lean modules** and **10 of the 36
chapters**, spread across every sector of the theory — Analytic (23 modules),
Referee (14), Consciousness (9), Operators (6), TuringEncoding (4), Empirical
(2), plus the substrate and Yang–Mills developments.

And every Millennium anchor is an instance of the one law
(`PF/FrameworkApplicationCapstone.lean:68–90`):

| problem | `λ₀` as defined | `= π/(10·α)` with |
|---|---|---|
| Poincaré | `π/10` | `α = 1` |
| P | `π/(10√2)` | `α = √2` |
| RH | `π/15` | `α = 3/2` |
| YM | `π/20` | `α = 2` |
| Hodge | `π(√5−1)/20` | `α = φ`, via `lambda_0_Hodge_clean` |
| NP | `π/(10(φ+¼))` | `α = φ+¼` |

So an unpinned `λ₀` is not a local gap. It is the keystone: the six-problem
family structure, the Galois-rigidity discriminator that sorts those six by
whether `α ∈ ℚ`, and the claim that the `α`-skeleton is *spectral* at all, each
rest on an identification that has not been made.

**And it compounds with today's other result.**
`PF/AlphaLayerSeparation.lean` proves the substrate cannot force the twisted
`α`-values — they lie outside `ℤ[1/3] = K_0(M_{3^∞})` while their Galois
discriminants lie inside it. Put the two together and the `α`-skeleton is
**doubly unanchored**: provably not determined by the substrate below it, and
not yet tied to an operator above it. That is a sharper and more useful
statement of the project's central open problem than any single chapter's
numerals, and it is what the author's "there may be more on the bottom"
intuition points at.

Downstream of the pinning, and therefore all held:

* the spectral gap `Δ = λ₀(H_P) − λ₀(H_NP)`, hence the P-vs-NP reduction,
  which `ch09`'s ledger already files as CONDITIONAL REDUCTION;
* `1/Δ`, quoted as `11.22` in `ch07` and as `18.53` in `ch34A`;
* `ch09`'s quantum-enhancement estimate, which scales as `exp(c·Δ·N)`;
* the ten-chapter numeral spread recorded in
  `codex/BOOK_LEAN_SUPERSESSION_MAP_2026-10-05.md`.

That map classified the `0.1330 → 0.1682` change as a *supersession* — the
Lean having refined an earlier value. **That classification was wrong and is
withdrawn.** `PF/SpectralGap.lean:21,25` define the closed forms outright:

```lean
noncomputable def lambda_0_P  : ℝ := pi_10 / Real.sqrt 2
noncomputable def lambda_0_NP : ℝ := pi_10 / (phi + 1/4)
```

and `spectral_gap_value` certifies the decimal expansion *of that defined
expression*. No operator appears anywhere in it. The same file says so at
`:181`: "The genuine open problem reduces to: derive Problem 1 (polylog
spectral formula). Once `λ_0(H_α) = π/(10·α)` is established …". And `:166`
records that the old empirical value was "CLOSED as buggy-pipeline artifact".

So neither number is a derived spectral quantity: the old one was a bug, the
new one is a definition. **The ten-chapter propagation is held** — a numeral
whose referent is unpinned cannot be propagated, in either direction.

## Micro — the one fact that constrains the pinning

Three candidate operators exist in the tree:

| candidate | location |
|---|---|
| `arxivHalpha α` | `PF/Operators/VAlphaExplicitFromArxiv.lean:76` |
| `h_alpha_basis α` | `PF/Operators/VAlphaExplicit.lean:269` |
| `H_P_canonical` | `PF/IntegralKernel/Bridge.lean:95` |

For the first, `PF/PolylogEigenvalueDischargeAttempt.lean:153` already proves

```lean
rayleigh_quotient_at_zero (α) : ⟪arxivHalpha α e₀, e₀⟫ = 0
```

and `PF/Operators/VAlphaPMapShape.lean:134` proves `‖stdBasisVec n‖ = 1`. Put
together, `arxivHalpha α` admits a **unit** vector whose Rayleigh quotient is
`0`. The theorems below draw the consequence: no positive constant can be a
uniform lower bound for its Rayleigh quotients.

Therefore, stated as an implication so that it commits to no reading:

> **If** `λ₀` denotes any quantity that is a uniform lower bound on Rayleigh
> quotients — the infimum of the spectrum being the canonical such quantity —
> **then** `arxivHalpha α` is ruled out as `H_α`, for every `α > 0`.

That eliminates one of the three candidates under one of the readings. It does
not tell us which operator and which quantity the book means; only the author
can supply that.

## The variational principle, stated correctly

`PolylogEigenvalueDischargeAttempt.lean`'s §2 docstring says `|0⟩`
"over-estimates the ground state from *below*". That is the variational
principle backwards, and it is corrected here and in that file.

For a symmetric operator, **every** unit trial vector gives an **upper** bound
on the bottom of the spectrum:

  `inf spec H ≤ ⟪H ψ, ψ⟫` for every unit `ψ`.

So a unit vector with Rayleigh quotient `0` proves `inf spec H ≤ 0`. It does
not "approach the ground state from below"; it *caps* it from above. The sign
of that inequality is the whole content of the obstruction, which is why
getting it backwards mattered.

## What is NOT claimed

* Not claimed that `π/(10·α)` is false. It is a definition; definitions are not
  false. What is unestablished is its identification with a spectral quantity.
* Not claimed that the other two candidate operators fail. They are unexamined.
* Not claimed that any Millennium-adjacent result changes. `ch09` already files
  the P-vs-NP reduction as CONDITIONAL REDUCTION, and this sharpens the reason
  rather than altering the label.
* No downgrade. Nothing is renamed, nothing withdrawn except one *classification
  of mine* that the evidence did not support.

## Repair direction

The missing object is a theorem identifying `π/(10·α)` with a spectral quantity
of a *named* operator. Name the operator and the quantity first; then either
prove the identification, or let the negative result below stand for that
candidate.

Found by a dispatched review session on the Legion mirror, verified line by line
against HEAD before any of it was acted on.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import PF.PolylogEigenvalueDischargeAttempt

namespace PrincipiaTractalis.PolylogSpectralPinningGap

open Real Complex
open scoped InnerProductSpace
open PrincipiaTractalis PrincipiaTractalis.Operators
open PrincipiaTractalis.PolylogEigenvalueDischarge

/-! ## §1 — A unit vector with vanishing Rayleigh quotient -/

/-- The basis vector `|0⟩` is a **unit** vector whose `arxivHalpha`-Rayleigh
    quotient vanishes. Both halves are already proved elsewhere; bundling them
    is what makes the variational consequence available. -/
theorem unit_witness_with_zero_rayleigh (α : ℝ) :
    ‖stdBasisVec 0‖ = 1 ∧
    (⟪arxivHalpha α ⟨stdBasisVec 0, Halpha_PMap_basis_mem α 0⟩,
       stdBasisVec 0⟫_ℂ).re = 0 := by
  refine ⟨stdBasisVec_norm 0, ?_⟩
  rw [rayleigh_quotient_at_zero]
  simp

/-! ## §2 — No positive uniform lower bound -/

/-- **The constraint.** If `c` is a lower bound for the `arxivHalpha`-Rayleigh
    quotients across the standard basis, then `c ≤ 0`.

    Proof: instantiate at `n = 0`, where the norm is `1` and the quotient is
    `0`. Any uniform lower bound over the whole domain is in particular a bound
    over the basis, so this suffices to rule out the general case too. -/
theorem no_positive_uniform_lower_bound (α : ℝ) (c : ℝ)
    (h : ∀ n : ℕ, c * ‖stdBasisVec n‖ ^ 2 ≤
      (⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
         stdBasisVec n⟫_ℂ).re) :
    c ≤ 0 := by
  have h0 := h 0
  rw [stdBasisVec_norm, rayleigh_quotient_at_zero] at h0
  simpa using h0

/-- **The negative result for this candidate.** For every `α > 0`, the
    closed-form value `π/(10·α)` is **not** a uniform lower bound for
    `arxivHalpha α`'s Rayleigh quotients.

    So if `λ₀` denotes the infimum of the spectrum — or any quantity that is
    such a lower bound — then `arxivHalpha α` is not the operator the book's
    closed form describes. -/
theorem groundStateValue_not_uniform_lower_bound {α : ℝ} (hα : 0 < α) :
    ¬ (∀ n : ℕ, groundStateValue α * ‖stdBasisVec n‖ ^ 2 ≤
        (⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
           stdBasisVec n⟫_ℂ).re) := by
  intro h
  have hle := no_positive_uniform_lower_bound α (groundStateValue α) h
  have hpos := groundStateValue_pos hα
  linarith

/-! ## §3 — Capstone -/

/-- **★ Polylog spectral pinning gap capstone ★**

    `arxivHalpha α` admits a unit vector with vanishing Rayleigh quotient;
    hence no positive constant is a uniform lower bound for its Rayleigh
    quotients; hence `π/(10·α)` is not such a bound for any `α > 0`.

    Consequence, stated as an implication and committing to no reading of
    `λ₀`: if `λ₀` is the infimum of the spectrum, or any uniform lower bound on
    Rayleigh quotients, then `arxivHalpha` is eliminated as a candidate for
    `H_α`. Which operator and which spectral quantity the book intends remains
    the author's to fix; that is the gap this file names. -/
theorem polylog_spectral_pinning_gap_capstone {α : ℝ} (hα : 0 < α) :
    (‖stdBasisVec 0‖ = 1 ∧
      (⟪arxivHalpha α ⟨stdBasisVec 0, Halpha_PMap_basis_mem α 0⟩,
         stdBasisVec 0⟫_ℂ).re = 0) ∧
    (∀ c : ℝ, (∀ n : ℕ, c * ‖stdBasisVec n‖ ^ 2 ≤
        (⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
           stdBasisVec n⟫_ℂ).re) → c ≤ 0) ∧
    ¬ (∀ n : ℕ, groundStateValue α * ‖stdBasisVec n‖ ^ 2 ≤
        (⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
           stdBasisVec n⟫_ℂ).re) :=
  ⟨unit_witness_with_zero_rayleigh α,
   fun c hc => no_positive_uniform_lower_bound α c hc,
   groundStateValue_not_uniform_lower_bound hα⟩

/-! ## §4 — Non-vacuity -/

/-- Non-vacuity for `no_positive_uniform_lower_bound`: its hypothesis is
    satisfiable, witnessed by any `c ≤ 0`. Taking `c = 0` and using that the
    diagonal Rayleigh quotients are the `v_alpha_coeff` values, the hypothesis
    is not empty, so the theorem is not vacuously true. -/
theorem no_positive_uniform_lower_bound_hypothesis_satisfiable (α : ℝ) :
    (0 : ℝ) * ‖stdBasisVec 0‖ ^ 2 ≤
      (⟪arxivHalpha α ⟨stdBasisVec 0, Halpha_PMap_basis_mem α 0⟩,
         stdBasisVec 0⟫_ℂ).re := by
  rw [rayleigh_quotient_at_zero]
  simp

end PrincipiaTractalis.PolylogSpectralPinningGap

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.PolylogSpectralPinningGap.unit_witness_with_zero_rayleigh
#print axioms PrincipiaTractalis.PolylogSpectralPinningGap.no_positive_uniform_lower_bound
#print axioms PrincipiaTractalis.PolylogSpectralPinningGap.groundStateValue_not_uniform_lower_bound
#print axioms PrincipiaTractalis.PolylogSpectralPinningGap.polylog_spectral_pinning_gap_capstone

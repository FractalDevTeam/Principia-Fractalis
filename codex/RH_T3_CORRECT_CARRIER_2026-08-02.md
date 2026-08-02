# RH front, stone 1: T₃ on its correct carrier — spectrum solved exactly, HP route redirected

**Date:** 2026-08-02. **Script:** `codex/rh_t3_hardy_space.py`. **Mission context:**
Pablo's directive to attempt the Millennium problems using the framework in its
entirety, creatively, under full rigor.

## The repair (new, positive result)

ch20's T₃ on L²([0,1],dx/x) is the wrong carrier (the corpus's own ch24
diagnosis). The obstruction to the right carrier — analytic functions — is the
√(x/y_k) weight's branch point at 0. **Conjugating by m(x) = √x removes it**:

    (T̃g)(x) = Σ_k ω_k · x/(x+k) · g((x+k)/3)

Rational weights (poles −1, −2 outside), branches contract D(1/2, 0.7) strictly
into itself ⇒ **T̃ is nuclear of order zero on H²(D)** by the classical Ruelle
argument. Conjugation preserves the spectrum. This is the first well-posed
formulation of the framework's RH operator.

## The spectrum, exactly

Truncation-stable to 4×10⁻¹⁵ across N = 30/60/120 (nuclearity confirmed):

    |λ| = 1, 1/3, 1/9, 1/27, …  = 3⁻ⁿ,   eigenvalues ≈ {1} ∪ {±i·3⁻ⁿ}

**Why**: the branches are AFFINE (y_k = (x+k)/3, derivative exactly 1/3
everywhere). For piecewise-affine full-branch maps the analytic-space transfer
spectrum is forced geometric in the branch multiplier. This is structural, not
numerical.

## Three consequences

1. **ch20's self-adjointness claim fails on the correct carrier**: the nonzero
   sub-leading eigenvalues are purely imaginary (±i·3⁻ⁿ), |Im|/|λ| = 1.000.
   (The L² "self-adjointness" was a statement about the symmetrized T₃^sym,
   whose L² spectrum the corpus already measured as dense-at-0 fog.)
2. **The base-3 affine system CANNOT be a Hilbert–Pólya operator.** A geometric
   sequence 3⁻ⁿ cannot be rescaled onto the ζ ordinates (which grow like
   2πn/log n). Measured: best one-parameter readout gives mean miss 8.8 vs
   null 1.18 — WORSE than random, because geometric decay concentrates all but
   finitely many eigenvalues below every ordinate. This is the analytic-side
   sibling of Wave 52B (no discrete ℕ→ℝ carrier at α = 3/2 hits Hardy 1914):
   **the linear base-3 projection of the substrate provably cannot carry the
   zeros. Anything that seemed to work on L² was truncation fog.**
3. **The creative continuation the framework itself points to**: Mayer 1991 —
   already cited in ch20, with the book's own c1 correction noting it concerns
   the SELBERG zeta — gets a genuine zeta function from a transfer operator
   precisely because the Gauss-map branches 1/(x+n) are NONLINEAR Möbius maps.
   The substrate's route to spectra-with-arithmetic-content must go through a
   nonlinear induced system, not the affine digit shift. Candidate: a base-3
   Möbius system y_k = 1/(x+k), k ∈ {1,2,3} (a "depth-3 Gauss map"), whose
   transfer operator on the same H² carrier is nuclear by the same argument
   and whose Fredholm determinant is a genuine dynamical zeta. Whether ITS
   zeta has any relation to Dirichlet L-functions mod 3 is the next
   falsifiable question — and unlike the affine case it is not pre-refuted.

## Standing rule extracted

Piecewise-AFFINE symbolic dynamics ⇒ geometric analytic spectrum ⇒ no
Hilbert–Pólya. Every future operator proposal in the corpus must pass this
one-line check before any numerics are run.

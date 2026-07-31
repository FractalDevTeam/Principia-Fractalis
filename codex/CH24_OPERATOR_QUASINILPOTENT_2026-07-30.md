# ch24's spectral operator is quasinilpotent: the rank mechanism is structurally impossible

This supersedes the "weak signal" reading of `CH24_OPERATOR_ILLPOSED_2026-07-30.md`.
The problem is not statistical power. **The operator as defined has at most one
nonzero eigenvalue, for any curve, so an eigenvalue multiplicity equal to
`rank E(Q) >= 2` cannot occur.**

## The defect

ch24 Definition (spectral-operator-bsd):

    (T_E f)(x) = sum_{p} (a_p/p) * exp(i*pi*alpha*D(p)*x) * f(x/p)   on L^2([0,1]).

Every symbol is `x -> x/p` with `p >= 2`. These all **contract toward the common
fixed point x = 0**. Consequence, entirely basis-free:

> If `supp f` is contained in `[a,1]` with `a > 0`, then `supp(T f)` is contained
> in `[pa, 1]`, which is empty once `pa > 1`. Since every good `p >= 2`, each
> application at least doubles the lower support bound, so `T^n f = 0` for
> `n > log_2(1/a)`.

`T` is therefore **locally nilpotent on functions vanishing near 0**, and its
entire spectrum is carried by the behaviour at the single fixed point `x = 0`.

## Numerical confirmation, three independent ways

Curve 389a1, s = 1.75, PMAX = 5000:

| discretization | matrix rank | nonzero eigenvalues |
|---|---|---|
| collocation, grid 240 | 81  | **1** |
| collocation, grid 480 | 161 | **1** |
| Galerkin cell-averaging, grid 240 | — | **1** |

The collocation matrix has **zero** nonzero entries strictly above the diagonal
and exactly **one** nonzero diagonal entry, at `(0,0)`. So its spectrum is
literally `{M[0,0]} u {0,...,0}`, and indeed `|M[0,0]| = |lambda_max| = 0.491928`
to six figures. Cell-averaging gives the same count, so it is not an artifact of
the interpolation.

## What this falsifies in ch24

1. **Theorem (Spectral Concentration), `thm:spectral-concentration-bsd`** — "the
   eigenvalues of `T_E` concentrate at `phi/e` with multiplicity equal to
   `rank E(Q)`". **False as stated.** There is at most one nonzero eigenvalue, so
   multiplicity `>= 2` is impossible; and the single value is not `phi/e`
   (it ranges over roughly 0.08–0.68 across the twelve curves tested).
2. **Conjecture (Rank Equality via Fractal Resonance),
   `conj:rank-equality-fractal`** — follows Theorem 1 and is **false as stated**,
   not merely unverified.
3. **Theorem (Self-Adjointness at `alpha = 3pi/4`), `thm:self-adjoint-bsd`** —
   also false. A strictly triangular matrix with one nonzero diagonal entry is as
   far from normal as possible; a self-adjoint operator with a single nonzero
   eigenvalue would be rank-one Hermitian, which this is not.

This also explains the earlier negative results without appeal to noise: the
2026-07-28 multiplicity counts (3, 11, 3, 10) came from the **Hermitian part**
`(T+T*)/2`, a different operator, because the operator's own spectrum has only
one nonzero point to count.

## The constructive repair, and its limit

The contraction is the whole problem, so the natural fix is the **expanding**
map — i.e. a transfer (Ruelle) operator, `f(x/p) -> f(p x mod 1)`. This does
restore a genuine spectrum:

| curve | rank | contracting: #nonzero eigs | expanding: #nonzero eigs |
|---|---|---|---|
| 11a1   | 0 | 1 | 240 |
| 37a1   | 1 | 1 | 240 |
| 389a1  | 2 | 1 | 240 |
| 5077a1 | 3 | 1 | 240 |

So an operator of ch24's general shape *can* have the spectral richness the
mechanism needs — but the specific `phi/e` claim still fails there:

```
multiplicity within 0.02 of phi/e (expanding operator)
  11a1  (r=0): 0      Hermitian part: 0
  37a1  (r=1): 0      Hermitian part: 4
  389a1 (r=2): 0      Hermitian part: 1
  5077a1(r=3): 2      Hermitian part: 3
```

No correspondence with rank, in either the full spectrum or the Hermitian part.

## Honest scope of this refutation

- It applies to the operator **as literally written** in ch24, on `L^2([0,1])`.
  The support argument is basis-free and does not depend on discretization.
- It does **not** show that no operator of this family can encode rank. The
  expanding variant is well posed and untested beyond the `phi/e` question.
- It says nothing about BSD, and nothing about the Lean corpus: r129–r164 are
  unconditional theorems about Mordell–Weil groups and never reference this
  operator.
- The two earlier defects stand and are independent: the `s = 1` weight is
  outside the convergence range `Re(s) > 3/2` that the chapter's own hypothesis
  `LSeriesAbsConvergenceForReSGreaterThanThreeHalves` assumes
  (`CH24_OPERATOR_ILLPOSED`), and the `phi/e` multiplicity never showed signal
  (`CH24_SPECTRAL_TEST`).

## Recommendation

ch24's spectral sections need reconstruction, not annotation:

1. Replace the contracting symbol `x -> x/p` with the expanding `x -> p x mod 1`,
   giving a transfer operator with genuine spectrum.
2. Use a weight `a_p / p^s` with `s > 3/2`, matching the chapter's own
   convergence hypothesis.
3. Re-derive what, if anything, the spectrum of *that* operator has to do with
   rank. The `phi/e` value should be treated as unsupported until re-derived: it
   currently rests on a theorem that is false for the operator as defined.
4. Research Problem 1 (`tr(T^n) = d^n/ds^n log L_f`) is untestable on the
   contracting operator, where `tr(T^n) = M[0,0]^n` identically. It becomes a
   real question only after step 1.

# ch24's spectral mechanism: the defect is the FUNCTION SPACE, not the map

Completes `CH24_OPERATOR_QUASINILPOTENT_2026-07-30.md`. Both natural readings of
ch24's operator fail, for **opposite** reasons, and neither admits a well-defined
"multiplicity of the eigenvalue `phi/e`".

## The two failures

**Contracting, as ch24 writes it: `f(x/p)`.** Every symbol contracts to the
common fixed point `x = 0`, so `T` is locally nilpotent on functions vanishing
near 0 (support argument, basis-free). Every discretization tried gives
**exactly one** nonzero eigenvalue; the collocation matrix is exactly
lower-triangular with a single nonzero diagonal entry. **Too few eigenvalues** --
a multiplicity `>= 2` is impossible.

**Expanding, the obvious repair: `f(px mod 1)`.** Restores a full spectrum, but
the truncations do not converge. At fixed `PMAX = 200`, refining the grid:

| grid | 200 | 400 | 800 | 1600 |
|---|---|---|---|---|
| `\|lam\|_max` | 0.4731 | 0.4871 | 0.4710 | **0.4376** |
| nonzero eigs | 200 | 400 | 800 | 1600 |
| `sum\|lam\|` | 61.1 | 121.8 | 243.6 | 487.1 |
| **`sum\|lam\|/grid`** | 0.3056 | 0.3045 | **0.3045** | **0.3045** |
| median `\|lam\|` | 0.324 | 0.332 | 0.329 | 0.330 |

`sum|lam|` grows **exactly proportionally to the grid** and the median eigenvalue
modulus stays bounded away from zero. Both are signatures of a **non-compact**
operator: the truncations carry ~`grid` eigenvalues of comparable size and have
no spectral limit. `|lam|_max` correspondingly wanders instead of settling.
**Too many eigenvalues, no discrete list** -- so "multiplicity of `phi/e`" is
again undefined, now for the opposite reason.

And at fixed grid the expanding operator is not even monotone in rank:

```
11a1 (r=0) 0.2149    37a1 (r=1) 0.5218    389a1 (r=2) 0.4901    5077a1 (r=3) 0.6376
```

rank 1 exceeds rank 2.

## The diagnosis

For "eigenvalue multiplicity equals `rank E(Q)`" to be a *meaningful* statement,
the operator must be **compact** (or at least quasi-compact) so that it has a
discrete spectrum with finite multiplicities. Neither the contracting nor the
expanding composition operator on `L^2([0,1])` is:

- composition with a contraction toward a common fixed point is quasinilpotent;
- composition with an expanding map on `L^2` is not compact.

Composition/transfer operators of expanding maps **do** become quasi-compact --
with genuinely discrete spectrum and finite multiplicities -- but only on
smaller spaces: holomorphic functions on a disc, or `C^k`/Hoelder spaces. That is
the classical Ruelle-Perron-Frobenius setting; the Gauss-Kuzmin-Wirsing operator
is the standard example, quasi-compact on an analytic space with a discrete
spectrum whose leading nontrivial eigenvalue is the GKW constant `0.3036...`.

**So the fixable defect is the choice of `L^2([0,1])`, not the choice of symbol.**
ch24 specifies `L^2([0,1])` (Definition, spectral-operator-bsd), which is the one
setting in which neither symbol gives a countable spectrum.

## A structural objection that survives any repair

Even granting a quasi-compact realisation, there is a problem of principle with
the shape of the claim. In the Ruelle setting the *eigenvalues* are determined by
the map and the weight. ch24 asks for a **universal** constant `phi/e`, the same
for every curve, with the **multiplicity** carrying the arithmetic. But the
curve enters only through the weights `a_p`, which multiply the whole operator --
so changing `E` moves the eigenvalues themselves rather than reproducing one
fixed eigenvalue with varying multiplicity. Nothing observed here shows a fixed
eigenvalue appearing `rank` times; what is observed is that the *whole spectrum*
shifts with the curve. A mechanism of the stated form -- fixed location, varying
multiplicity -- would need a reason for `phi/e` to be an eigenvalue of every
`T_E`, and no such reason is given or found.

## Where that leaves the chapter

- `thm:spectral-concentration-bsd`, `conj:rank-equality-fractal`,
  `thm:self-adjoint-bsd`: false as stated (previous document), and the repair
  attempted here does not rescue them.
- The `s = 1` weight is separately outside the convergence range `Re(s) > 3/2`
  that the chapter's own hypothesis assumes (`CH24_OPERATOR_ILLPOSED`).
- The `phi/e` value has no surviving derivation or numerical support.
- The chapter's *intuition* -- rank is readable from `a_p/p` data -- remains
  classically true via Mestre-Nagao, and that route needs no operator at all.
  It is a statement about a Dirichlet sum, and it is where the chapter's
  computational content actually lives.

## Recommendation

The honest reconstruction of ch24's spectral sections is: **drop the operator
formalism** and state the Mestre-Nagao content directly, as a conditional
numerical heuristic about `sum_{p<X} a_p/p`. If an operator formulation is
wanted, it must be built on an analytic or Hoelder space where quasi-compactness
holds, and the fixed-location/varying-multiplicity structure needs an argument
that does not currently exist.

None of this touches the Lean corpus: r129-r164 are unconditional theorems about
Mordell-Weil groups and never reference this operator.

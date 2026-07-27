# The non-torsion arc — wall map (started 2026-07-27)

## Goal

Discharge `NonTorsionCertificate` (r129, `PF/MordellWeilRankLowerBound_r129.lean`)
for one explicit point of one 17-cohort curve, yielding the corpus's first
kernel-verified literal `Module.rank` bound for an LMFDB curve:

```
1 ≤ Module.rank ℤ (E_37a1).Point        -- E: y² + y = x³ − x,  P = (0, 0)
```

## Route decision (2026-07-27 audit, both agents + pin inspection)

Rejected routes:
- **Torsion-injection under reduction** — needs a point-level reduction map +
  kernel torsion-freeness (formal groups). Pin's `Reduction.lean` has
  integral/minimal-model *definitions only*. Months of new theory.
- **Lutz–Nagell** — same formal-group/valuation machinery.
- **Explicit multiples alone** — insufficient without a torsion bound (no Mazur).
- **Heights from mathlib** — `Mathlib/NumberTheory/Height/` and
  `GroupTheory/Descent.lean` are master-2026 only, NOT on our v4.24 pin, and
  even upstream the point-height + parallelogram law are TODO.

**Chosen: the single-curve height machine.** For the FIXED curve 37a1, prove
the duplication height inequality with an explicit constant, then let 4ⁿ
growth beat any finite orbit. Everything is elementary: integer polynomial
identities (`ring`/`decide`), gcd/resultant bounds, max-abs estimates, and
concrete point arithmetic by `norm_num`. No new theory imported.

## The wall, stone by stone

- **B1 (r130) — naive height on ℚ.** `naiveHeight q = max q.num.natAbs q.den`.
  API: positivity, height of integers, finite sets have bounded height,
  unbounded-height sequence ⟹ infinite range. Small, self-contained.
- **B2 — the duplication formula for 37a1 as an explicit rational identity.**
  From the pin's `Affine.slope`/`addX` (`Affine/Formula.lean:166,238`):
  for affine `P = (x, y)` on 37a1 not 2-torsion,
  `x(2P) = f(x)/g(x)` with `f = x⁴ + 2x² − 8x·? ...` (derive exactly; for
  y² + y = x³ − x: ψ₂² = 4x³ − 4x + 1, f = x⁴ + 2x² + ... — compute
  symbolically and certify against `addX` by `field_simp`/`ring`).
  Also: the cubic `4x³ − 4x + 1` has NO rational roots (rational root theorem,
  finitely many candidates, `norm_num`) ⟹ no rational affine point of 37a1 is
  2-torsion ⟹ doubling never leaves the affine chart. This kills the
  chain-hits-O case globally.
- **B3 — the resultant/gcd bound (the hard stone).** Homogenize: F(a,b),
  G(a,b) of degree 4 with Res(F,G) = R ≠ 0 explicit. Bézout-style identities
  `p·F + q·G = R·a⁷`, `r·F + s·G = R·b⁷` (explicit integer polynomials,
  certified by `ring`) give: for coprime (a,b), `gcd(F(a,b), G(a,b)) ∣ R`.
  Plus the elementary lower bound `max(|F(a,b)|, |G(a,b)|) ≥ c·max(|a|,|b|)⁴`
  (from the same identities: R·a⁷ and R·b⁷ are ℤ-combinations of F,G with
  coefficient polynomials of degree 3 ⟹ `|R|·H⁷ ≤ κ·max(|F|,|G|)·H³`).
- **B4 — the duplication inequality.** Assemble B2+B3:
  `naiveHeight (x 2P) ≥ naiveHeight (x P)^4 / κ'` i.e. in log-free ℕ form:
  `κ' * naiveHeight (x 2P) ≥ naiveHeight (x P)^4` with κ' explicit.
- **B5 — assembly.** (i) Compute Q = 2^k·P concretely by `norm_num` through
  the group law until `naiveHeight (x Q)^4 > κ'^2 · naiveHeight (x Q)` margin
  guarantees strict growth forever (explicit threshold: h > κ' suffices since
  then h(next) ≥ h⁴/κ' > h·(h²/κ') > h). Known: ĥ(P) ≈ 0.0511 ⟹ k = 4 or 5
  should clear any reasonable κ'. (ii) Strict monotone height along the chain
  ⟹ the multiples `2^n·Q` are pairwise distinct ⟹ `Set.range (fun n => 2^n • Q)`
  infinite ⟹ `¬IsOfFinAddOrder Q` (torsion ⟹ finite zmultiples set)
  ⟹ `¬IsOfFinAddOrder P` (P torsion would make Q torsion)
  ⟹ r129's `mordellWeil_rank_ge_one` fires. FLAG.

## Ground truth for B2/B3 (verify symbolically before Lean)

For W: y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆ with (a₁,a₂,a₃,a₄,a₆) = (0,0,1,−1,0):
- ψ₂²(x) = 4x³ + b₂x² + 2b₄x + b₆ where b₂ = 0, b₄ = −2, b₆ = 1
  ⟹ g(x) = 4x³ − 4x + 1.
- f(x) = x⁴ − b₄x² − 2b₆x − b₈ where b₈ = −1 ⟹ f(x) = x⁴ + 2x² − x·2·1... 
  COMPUTE EXACTLY with sympy first (`x(2P) = (x⁴ − b₄x² − 2b₆x − b₈)/ψ₂²`);
  certify the Lean form against `addX x x (slope x x y y)` by `field_simp; ring`.
- Res(f, g) as integer; the four Bézout cofactor polynomials via sympy
  `gcdex`/resultant subresultants, cleared to ℤ. All identities then `ring`.

## Status

- 2026-07-27: route chosen, plan written. B1 = r130 in progress.
- Point P = (0,0) IS on 37a1: 0² + 0 = 0³ − 0. ✓ (also already verified
  on-curve in the corpus's Heegner files for 37a1.)

## Rules of the arc (same as the UHF summit)

Agent proves → independent rebuild → fresh transitive `#print axioms` →
commit → push. No `native_decide`. No `Prop := True`. Every conditional
states its hypothesis in the theorem, not in prose.

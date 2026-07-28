# The independence arc — rank ≥ 2 (389a1) and rank ≥ 3 (5077a1)

Started 2026-07-28, at Pablo's direction: "go for the big ticket items."

## The prize

Kernel-verified `2 ≤ Module.rank ℤ E389a1(ℚ)` and
`3 ≤ Module.rank ℤ E5077a1(ℚ)`. Point INDEPENDENCE has never been
formalized in any prover. This is the honest summit of the BSD axis short
of L-functions: 389a1 and 5077a1 are THE historically famous rank-2 and
rank-3 curves (389a1 = smallest conductor rank 2; 5077a1 = smallest
conductor rank 3, the Buhler–Gross–Zagier curve).

## Why it is reachable (feasibility verified 2026-07-28)

The strategy is the height-regulator argument done with EXPLICIT constants,
exactly like the non-torsion arc but two-dimensional:

1. The canonical height ĥ(R) = lim h(x(2ⁿR))/4ⁿ exists with an explicit
   window |ĥ − h| ≤ C once the duplication bound is TWO-sided. We have the
   lower side (r133-style, per curve). The upper side is the EASY triangle
   inequality: |F|, |D| ≤ (coeff-sum)·H⁴.
2. **The linchpin — VERIFIED by sympy for 389a1**: the addition sum/product
   identities are y-free after reduction mod the curve equations:
     (x₁−x₂)²·(x(P+Q) + x(P−Q)) = 2x₁²x₂ + 2x₁x₂² + 4x₁x₂ − 4x₁ − 4x₂ + 1
     (x₁−x₂)^k·(x(P+Q) · x(P−Q)) = explicit symmetric polynomial
   So x(P+Q), x(P−Q) are the two roots of T² − S·T + P = 0 with S, P
   explicit rational functions of x₁, x₂ — and the quasi-parallelogram law
     |h(P+Q) + h(P−Q) − 2h(P) − 2h(Q)| ≤ C₂
   follows from 2-variable Bézout/resultant bounds (sympy-derivable,
   `ring`-certifiable) + elementary quadratic-root height bounds.
   This is Silverman VIII.6 specialized to ONE curve = finite arithmetic.
3. From quasi-parallelogram + duplication: ĥ is a QUADRATIC form on E(ℚ)
   (exact parallelogram in the limit), ĥ(torsion) = 0, and ĥ(R) = 0 ⟹ R
   torsion (bounded orbit + Northcott-for-ℚ finiteness, the r134 trick).
4. Independence: for P, Q the known generators, compute rational intervals
   for ĥ(P), ĥ(Q), ĥ(P+Q) via h(2ⁿ·—)/4ⁿ with the ±C/4ⁿ window (norm_num,
   exact ℚ arithmetic), and verify the regulator
     det [[ĥP, ⟨P,Q⟩], [⟨P,Q⟩, ĥQ]] > 0,  ⟨P,Q⟩ = (ĥ(P+Q) − ĥP − ĥQ)/2.
   Positive definiteness ⟹ (mP + nQ = 0 → q(m,n) = 0 → m = n = 0)
   ⟹ ℤ² ↪ E(ℚ) ℤ-linearly ⟹ rank ≥ 2 (lift_rank_le_of_injective, ℤ²).
   For 5077a1: 3×3 regulator with generators (−2,3), (−1,3), (0,2) —
   Sylvester criterion on three leading minors, same window technique.

Known numerics (sanity targets, not proofs): 389a1 ĥ-regulator ≈ 0.1524;
5077a1 regulator ≈ 0.417. Both comfortably nonzero — the windows need only
be tight enough, and each extra doubling shrinks the window by 4×.

## The stones

- **W0 (r143/r144)** — the per-curve substrate: dbl_x + quartic duplication
  LOWER bound for 389a1 (κ=1728) and 5077a1 (κ=105754), rank ≥ 1 falls out
  as a corollary. Ground truth in cohort_data_pack.txt (verified).
- **W1** — duplication UPPER bound: h(x(2P)) ≤ 4h(x) + c (triangle
  inequality on |F|, |D| ≤ c·H⁴; trivial vs B3). Gives the two-sided window.
- **W2 (the hard stone)** — quasi-parallelogram for the fixed curve:
  homogenize S(x₁,x₂), P(x₁,x₂) in two coordinate pairs (a₁,b₁,a₂,b₂);
  2-variable Bézout certificates (sympy elimination, per curve) give
    max-height(quadratic coeffs) ≍ H₁²·H₂² within explicit constants;
  quadratic-root height bounds tie h(x₃) + h(x₄) to the coefficient heights
  (both directions; root-coefficient inequalities are elementary).
  Deliverable: |h(x(P+Q)) + h(x(P−Q)) − 2h(x P) − 2h(x Q)| ≤ C₂, explicit.
  Degenerate cases (P = ±Q, x₁ = x₂) handled via the existing duplication
  bound and h(O)-conventions.
- **W3** — the canonical height: ĥ(R) := lim h(2ⁿR)/4ⁿ as a real number
  (Cauchy with explicit modulus from W1+r133 two-sidedness; mathlib Real
  completeness). API: |ĥ − h| ≤ C, ĥ(2R) = 4ĥ(R), exact parallelogram (W2
  + limit), ĥ(mR) = m²ĥ(R), ĥ ≥ 0, ĥ(R) = 0 ↔ R torsion (Northcott-for-ℚ:
  bounded naive height ⟹ finitely many rationals ⟹ finite orbit ⟹ torsion —
  the r134 argument run backward).
- **W4** — regulator windows by norm_num: rational lower/upper bounds for
  ĥ(P), ĥ(Q), ĥ(P±Q) from finitely many chain heights; interval arithmetic
  in ℚ; det > 0.
- **W5** — the flag: q(m,n) = ĥ(mP+nQ) positive definite on ℤ² ⟹ the map
  ℤ² → E(ℚ), (m,n) ↦ mP+nQ is injective ⟹
  `2 ≤ Module.rank ℤ E389a1(ℚ)`. Then the 3×3 version for 5077a1 ⟹
  `3 ≤ Module.rank ℤ E5077a1(ℚ)`.

## Ground truth status

- 389a1 (a=(0,1,1,-2,0), gen (0,0)): f = x⁴+4x²−2x+3, g = 4x³+4x²−8x+1,
  no rational 2-torsion, Bézout κ = 1728, chain 0→3→114/121→1169154495/…,
  clears at index 3. VERIFIED.
- 5077a1 (a=(0,0,1,-7,6), gen (−2,3)): f = x⁴+14x²−50x+49, g = 4x³−28x+25,
  no rational 2-torsion, Bézout κ = 105754, chain −2→221/49→3009638454/…,
  clears at index 2. VERIFIED.
- 389a1 addition identities: y-free reductions VERIFIED (see above).
  Full W2 certificate suite (homogenized 2-variable Bézout cofactors,
  both curves, second generators for the regulator bases) still to compute.
- Generator bases for the regulators: 389a1: P=(0,0), Q=(1,0) (LMFDB
  generators — VERIFY (1,0) on-curve: 0+0 = 1+1−2 = 0 ✓). 5077a1:
  (−2,3), (−1,3), (0,2) (verify: 9+3=−8+4+14=... check in sympy pass).

## Rules

Same as the non-torsion arc: sympy-verify every identity before Lean;
agent proves → independent rebuild → fresh transitive #print axioms →
commit → push. No native_decide, no sorry, no Prop := True. Honest scope
in every file: lower bounds only, no L-functions, no BSD claims.

## W2 ground truth — VERIFIED CLEAN FORMS (sympy, 2026-07-28)

x(P+Q) and x(P−Q) are the two roots of `T² − S·T + Pr = 0` where, with
dd = (x₁−x₂)²:

- **389a1**: S = (2x₁²x₂ + 2x₁x₂² + 4x₁x₂ − 4x₁ − 4x₂ + 1)/dd,
  Pr = (x₁²x₂² + 4x₁x₂ − x₁ − x₂ + 3)/dd
- **5077a1**: S = (2x₁²x₂ + 2x₁x₂² − 14x₁ − 14x₂ + 25)/dd,
  Pr = (x₁²x₂² + 14x₁x₂ − 25x₁ − 25x₂ + 49)/dd

(Note Pr's numerator is the classical biquadratic form B(x₁,x₂) whose
diagonal B(x,x) recovers the duplication data — the structural sanity
check passes.) Regulator bases verified on-curve: 389a1 P=(0,0), Q=(1,0);
5077a1 (−2,3), (−1,3), (0,2).

## Status

- W0 389a1 = r143 DONE (pushed): dbl_x + κ=1728 quartic bound + rank ≥ 1.
- W0 5077a1 = r144 in progress (agent).
- Next: W1 (upper duplication bounds, easy), then W2 homogenized Bézout
  certificates for the quadratic coefficients (2-variable elimination,
  sympy), then W3 (ĥ as limit).

## W2 certificates — COMPUTED AND VERIFIED (2026-07-28, 42 PASS assertions)

Full suite in codex/W2_CERTIFICATES_389a1.md (+ cofactors txt + regenerating
python script). Highlights:
- **m = 2**: det of the (a₁,b₁)-coefficient matrix of (DD,S,P) is −R6 with
  R6(a,b) = 2a⁶+4a⁵b−20a⁴b²+10a³b³−30a²b⁴−8ab⁵+11b⁶ (irreducible, κ=85);
  Cramer cofactors give u·DD+v·S+w·P = R6(a₂,b₂)·b₁² and ·a₁².
- Pairwise certificates land EXACTLY on the r143 forms: ρ's are G3², F²,
  b₂²G3², F² — controlled by the already-kernel-verified r131/r143 layer.
- Level-2: α·G3²+β·F² = 389³·b₂¹³ / 389³·a₂¹³; R6-vs-F and R6-vs-G3
  certificates with 389². Minimality PROVED by lattice HNF (389 sharp for
  (G3,F) — r143's identity is optimal; obstruction = irreducible quadratic
  gcd(f,g) mod 389).
- **Content bound: gcd(DD,S,P) ∣ 389³** at fully coprime points.
- Symmetry under pair swap verified — (a₂,b₂)-side certificates are free.
- Lean-phase note: compose L1/L2 identities as separate ring lemmas
  (expanded corners have κ ~ 10⁹).

Status update: W0 ✓✓ (r143,r144), W1 ✓✓ (r145,r146), W2 ground truth ✓
(Lean formalization = next stone), W3 in progress (agent).

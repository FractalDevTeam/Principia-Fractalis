# r120 CLOSED — the RH on-line-zero atom is discharged

**Date:** 2026-07-25 · **Source commit:** `659acca5` · **Verified:** fresh transitive `#print axioms`

## The theorem

```lean
theorem positiveOnLineZetaZeroOrdinatesNonempty :
    PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty
```

unfolding to: **∃ t > 0 with `riemannZeta ⟨1/2, t⟩ = 0`** — at least one zero of ζ lies on
the critical line.

```
#print axioms positiveOnLineZetaZeroOrdinatesNonempty
  → [propext, Classical.choice, Quot.sound]
```

**No `Lean.ofReduceBool`.** That absence is the proof that `native_decide` was never used —
the advertised axiom budget of the entire RH chain is intact. No `sorry`, no project axioms.

## Build evidence

| item | value |
|---|---|
| interval-panel modules | **63 / 63 green** |
| midpoint panels | 474 |
| `decide +kernel` facts | 165 panels + 16 transcendental constants |
| panel failures | **0** |
| capstone build | 2863 jobs, 17 s |
| panel wall-clock | ~2.5 h, serial (parallel `-j12` OOMs a 15.7 GB box) |

## The proof

`Xi 1 < 0` and `Xi (77/5) > 0` by certified interval arithmetic, then the intermediate
value theorem via `xi_sign_change_implies_on_line_zero` (r115) produces the zero.

Certified error budget at `b = 15.4` (argmax of `Xi` between the first two zeros, hence the
largest budget available):

| source | bound |
|---|---|
| composite midpoint quadrature | ≈ 3.6e−6 |
| tail, `T = 5` | ≤ 1.1e−7 |
| ω-truncation, `N = 3` | ≤ 1e−12 |
| **⟹ certified `Xi(15.4) ≥`** | **2.93e−6 > 0** |

against `|Xi(15.4)| = 6.68e−6`. The endpoint `a = 1` is free: at `T = 1` the finite integral
is empty, so `Xi 1 = −0.8 + tail` with `|tail| ≤ 0.03`, needing zero quadrature nodes.

Enabling brick: `abs_thetaTermD2_le_exp` keeps the `e^{−π(n+1)²u}` factor rather than
collapsing it at `u = 1`, dropping `M` from 12.35 to 0.0042 at `u = 4` and the panel count
from ~4060 to 474.

## Honest scope — what this is NOT

**This is not the Riemann Hypothesis.** It is the classical fact (Hardy 1914; the first zero
sits at `t = 14.1347`) that *at least one* zero lies on the critical line. RH asserts that
*every* nontrivial zero does.

What it is: the **last bucket-1 item** (standard-but-unformalized) on the framework's RH
reduction chain. Discharging it feeds `rh_wave58_countability_reduction_capstone` and
collapses the honest RH residual to exactly two things:

1. the Hilbert–Pólya program conjecture — **bucket 3**, equivalent to RH itself;
2. the empirical-α pin — **bucket 2**, and shown *circular* in
   `ALPHA_NP_DERIVABILITY_2026-07-25.md`.

## Correction recorded

An earlier scouting note (mine) gave `Ξ(12) = +8.8e−3`, `Ξ(16) = −7.7e−4`. That used the
classical `Ξ = ½s(s−1)π^(−s/2)Γ(s/2)ζ(s)`, whereas the corpus's `Xi t = Re Λ(1/2+it)`
**omits** the `½s(s−1)` factor — which equals `−(1/4+t²)/2 < 0` on the critical line. The
corpus `Xi` therefore has the **opposite sign** and magnitudes ~128× smaller. Verified at 40
digits: `Xi(14) = −2.05e−6`, `Xi(15.4) = +6.68e−6`. The real budget was 6.7e−6, not 7.7e−4.

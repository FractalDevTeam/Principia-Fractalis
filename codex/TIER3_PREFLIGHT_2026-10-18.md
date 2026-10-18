# Tier-3 pre-flight: the two foundation claims hold (one needs a correction), the derivative layer the spec needs does not exist at all, and the one thing that could have killed the route is measured safe

**Date:** 2026-10-18 (Legion). Verification against the tree. No Lean written.
Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**. Script:
`codex/tier3_preflight_verify.py`.

---

## FIRST, A LIMIT ON WHAT I CAN ANSWER

**DeepSeek's boundary-analysis build spec is not in the tree.** `grep` over
`codex/*.md` and the whole repo finds no boundary-analysis spec and exactly one
DeepSeek mention — my own CI note. So:

* **Checks 1–4 are answered**, because each names a specific declaration and a
  specific property; those are verifiable without the spec text.
* **Check 5 ("any other API gaps between the spec and the tree") is NOT
  answerable.** I cannot diff against a document I do not have. What I give
  instead is the gap list for *a second integration by parts* — the only thing
  `ibp_phase` + a boundary analysis can mean here — and I label it **inferred**.
  **If the spec wants something else, this list is the wrong list.**

**Before the Acer commits weeks: paste the spec into `codex/`.** That is a
five-minute action that converts the inferred half of this report into a
verified one.

---

## VERDICT

| # | claim | verdict |
|---|---|---|
| 1 | `completedRiemannZeta₀_eq_theta_integral`, every `s : ℂ` | ✅ **exactly as stated** |
| 2 | `ibp_phase` takes arbitrary `F, F', c` | ⚠️ **generic in `F, F'`; `c` must be PURELY IMAGINARY** |
| 3 | second/third derivative lemmas | ❌ **absent — only first derivative exists** |
| 4 | `F_plus_tendsto_atTop_zero` right shape for the derivative version | ❌ **right shape for `F`; the derivative version must be built** |
| 5 | other gaps | **4 more, listed in §5 — inferred, not spec-verified** |

**The spec's foundation is sound. Its derivative layer is 100% unbuilt.** That
is the whole build, and it is larger than "lemmas the spec needs" suggests.

---

## 1. `completedRiemannZeta₀_eq_theta_integral` — CLEAN. FACT

`PF/Analytic/XiThetaIntegral.lean:366`:

```lean
theorem completedRiemannZeta₀_eq_theta_integral (s : ℂ) :
    completedRiemannZeta₀ s
      = ∫ x in Ioi (1 : ℝ),
          ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) * ((omega x : ℝ) : ℂ)
```

**Unrestricted `(s : ℂ)`, no hypotheses, no side conditions.** Exactly the
stated generality. Nothing to do.

## 2. `ibp_phase` — GENERIC IN `F, F'`, BUT NOT IN `c`. FACT

`PF/Analytic/Lambda0IBPIdentity_2026_10_15.lean:306`:

```lean
theorem ibp_phase {F F' : ℝ → ℝ} {c : ℂ} (hc : c ≠ 0) (hcre : c.re = 0)
    (hFderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt F (F' x) x)
    (hFcont0 : ContinuousWithinAt F (Ici 0) 0)
    (hFtop   : Tendsto F atTop (𝓝 0))
    (hFint   : IntegrableOn (fun u => ((F u : ℝ) : ℂ) * Complex.exp (c * u)) (Ioi 0))
    (hF'int  : IntegrableOn (fun u => ((F' u : ℝ) : ℂ) * Complex.exp (c * u)) (Ioi 0)) :
    ...
```

`F` and `F'` are genuinely arbitrary. **`c` is not: `hcre : c.re = 0` restricts
it to the imaginary axis.** For the Riemann edge that is free (`c = ±i·t/2`,
discharged by `re_phase_plus` / `re_phase_minus`), so **no work is created** —
but a spec written as "arbitrary `c`" is wrong about what it may instantiate,
and `norm_exp_mul_ofReal` (`:72`) shows why the restriction is structural: the
proof needs `‖exp(c·x)‖ = 1`.

**The operative cost is the six hypotheses, which must be supplied afresh for
every application.** §3–§5 are precisely the six, re-asked for `F := deriv F_plus`.

## 3. Second/third derivatives — ABSENT. FACT

**Present (first order only), `OmegaDerivative_2026_10_14.lean`:** `omega'`
(`:41`), `hasDerivAt_omega_term` (`:45`), `summable_omega_term_deriv_bound`
(`:79`), `omega_hasDerivAt` (`:120`), `omega'_nonpos` (`:162`),
`F_minus_hasDerivAt` (`:231`), `F_plus_hasDerivAt` (`:239`),
`differentiableOn_omega` (`:257`), `deriv_omega_eq` (`:262`).
`OmegaDerivativeBounds_2026_10_15.lean` adds first-derivative sign, bounds and
integrability.

**Absent — all six probes return nothing:** `omega''`,
`HasDerivAt (deriv F_plus)`, `deriv (deriv F_plus)`, `Continuous (deriv F_plus)`,
`IntegrableOn (deriv (deriv …))`, and any `iteratedDeriv` on these objects.
**There is no second derivative anywhere in the tree, and no third.**

**But the construction template is in the same file and the second order is a
mechanical mirror of it. JUDGEMENT.** `omega_hasDerivAt` (`:120–149`) is
`hasDerivAt_tsum_of_isPreconnected` applied with a uniform summable bound on
`Ioi δ`, `δ = x/2`. The second derivative needs: `omega''` as the termwise
`tsum` with one further factor `−π(n+1)²`, a `hasDerivAt_omega'_term`, a
`summable_omega'_term_deriv_bound` of the same shape, and the same application.
**No new idea, ~110–150 L.** `F_plus''` then follows by the product rule on
`e^{u/2}·ω(e^u)`, which has four terms rather than two — call it another
~80–120 L.

## 4. `F_plus_tendsto_atTop_zero` — RIGHT SHAPE FOR `F`, DERIVATIVE VERSION MISSING. FACT

`OmegaDerivativeBounds_2026_10_15.lean:268`:
`theorem F_plus_tendsto_atTop_zero : Tendsto F_plus atTop (nhds 0)` — exactly
the shape `hFtop` wants, and already consumed that way at
`Lambda0IBPIdentity:426`.

**`Tendsto (deriv F_plus) atTop (nhds 0)` does not exist and must be built.**
**MEASURED — it is true, and comfortably:**

| u | `F₊` | `D¹F₊` | `D²F₊` |
|---|---|---|---|
| 0 | 4.32e−2 | −1.14e−1 | +1.66e−1 |
| 1 | 3.22e−4 | −2.59e−3 | +1.81e−2 |
| 2 | 2.25e−10 | −5.12e−9 | +1.11e−7 |
| 3 | 1.77e−27 | −1.11e−25 | +6.81e−24 |
| 4 | 2.38e−74 | −4.07e−72 | +6.91e−70 |

The corpus already has the ingredient: `F_plus_le_exp_bound` (`:487`) plus
`tendsto_exp_neg_pi_mul_atTop_zero` (`:207`) is the pattern, re-run for the
derivative. ~60–100 L.

## 5. The other gaps — four more, for a second IBP. INFERRED, not spec-verified

To instantiate `ibp_phase` a second time with `F := deriv F_plus`, all six
hypotheses are needed for it. Three are §3/§4 above; the rest:

| needed | status | note |
|---|---|---|
| `ContinuousWithinAt (deriv F_plus) (Ici 0) 0` | ❌ absent | follows from `Continuous (deriv F_plus)`, itself absent; mirrors `F_plus_continuous` (`:174`) |
| `IntegrableOn (deriv (deriv F_plus)) (Ioi 0)` | ❌ absent | see the route note below |
| the new boundary constant `deriv F_plus 0` | ❌ absent | **MEASURED** `= ω(1)/2 + ω′(1) = −0.1141956486`; for the minus branch `deriv F_minus 0 = ω′(1) = −0.1358043514`. Both **nonzero**, so the second IBP introduces a genuinely new constant needing its own lemma, the analogue of `F_plus_zero` (`:405`) |
| `0 ≤ deriv (deriv F_plus)` on `Ioi 0` | ❌ absent | needed only by the cheap integrability route |

### The one thing that could have killed the route, and it is safe. MEASURED

`integrableOn_deriv_F_plus` (`:389`) is proved by
**`integrableOn_Ioi_deriv_of_nonpos`**, which needs the derivative to have a
**sign**. So the obvious question is whether that transfers to the second
derivative — i.e. whether `F_plus` is convex.

**I predicted it would NOT (that `F₊″` changes sign) and I was wrong.**
Measured: `D²F₊ > 0` at every sampled point of `[0, 4]` (table above, from
`+0.166` at `u=0` down to `+6.9e−70`), **no sign change**. `F_plus` is convex
there, so:

* **`integrableOn_Ioi_deriv_of_nonneg` is the right tool and it EXISTS** —
  `mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:755` (with a primed
  variant at `:787`). The existing `integrableOn_deriv_F_plus` proof transfers
  **verbatim** with `nonpos → nonneg`.

**Two routes to the second-derivative integrability, and the choice is the main
cost decision. JUDGEMENT:**

1. **Sign route** — prove `0 ≤ F₊″` on `Ioi 0`, then `integrableOn_Ioi_deriv_of_nonneg`.
   Cheap *if* the sign lemma is cheap. **It is the risk:** the first-order
   analogue `deriv_F_plus_nonpos_on_Ioi` (`:151`) needed the whole `crossTerm`
   apparatus (`crossTerm`, `crossTerm_nonpos`, `summable_crossTerm`,
   `omega_plus_cross_eq_tsum`, `omega_prime_cross_term_nonpos` — `:47–150`), and
   the second order needs its own. **~200–400 L, and this is where weeks go.**
2. **Bound route** — an explicit exponential majorant for `F₊″` plus dominated
   convergence, following `F_plus_le_exp_bound` (`:487`) → `F_plus_integrable_Ioi`
   (`:542`). **Avoids the sign lemma entirely**, and the measured decay
   (`6.9e−70` by `u=4`) makes the majorant easy.
   **Recommend route 2, and fall back to route 1 only if a majorant resists.**
   This is the same trade that just paid off in the residue build, where an
   exponential majorant beat a subdivision 6×.

## 6. Foundation verified kernel-clean, not assumed. FACT

Re-elaborated with `lake env lean` (which always emits, unlike the `lake build`
path the vacuous CI gate uses):

| file | EXIT | errors | axiom records | off-bar |
|---|---|---|---|---|
| `XiThetaIntegral.lean` | 0 | 0 | 16 | **0** |
| `Lambda0IBPIdentity_2026_10_15.lean` | 0 | 0 | 19 | **0** |
| `OmegaDerivative_2026_10_14.lean` | 0 | 0 | 13 | **0** |

48 records, all at or below `[propext, Classical.choice, Quot.sound]`.

**Note, carried over from the CI diagnosis:** none of the pilot boxes is
imported by `PF.lean` and nothing else imports them, so the Tier-3 target area
is **outside CI's build closure entirely** — CI neither builds nor axiom-checks
it. Not a blocker for the build; a blocker for trusting a green badge about it.

---

## 7. Cost, and the one next action

| piece | lines | risk |
|---|---|---|
| `omega''` termwise construction (mirror of `:120–149`) | 110–150 | low — template exists |
| `F_plus''`, `F_minus''` by product rule | 80–120 | low |
| `Tendsto (deriv F_plus) atTop 0` + continuity | 60–100 | low |
| `deriv F_plus 0 = ω(1)/2 + ω′(1)` and the minus analogue | 40–80 | low |
| **`IntegrableOn (deriv (deriv F_plus))`** | **100–400** | **HIGH — route 1 vs route 2 (§5)** |
| second `ibp_phase` application + the new identity | ~100 | low |
| **total** | **~500–950** | concentrated in one row |

**One next action: settle the second-derivative integrability route before
anything else is written.** Build `F_plus''` and an explicit exponential
majorant for it (route 2) first; if that majorant lands, the remaining rows are
all low-risk mirrors of existing code and the Acer's weeks estimate is
pessimistic. If it resists, route 1's cross-term analysis is the real project
and the estimate should be re-made then, not now.

---

## Label summary

* **FACT (quoted/verified from source):** `completedRiemannZeta₀_eq_theta_integral`'s
  unrestricted signature at `XiThetaIntegral:366`; `ibp_phase`'s full signature
  including `hcre : c.re = 0` at `Lambda0IBPIdentity:306`; the complete
  first-derivative inventory and the total absence of second/third derivatives
  (six probes, all empty); `F_plus_tendsto_atTop_zero` at `:268` and the absence
  of its derivative analogue; `integrableOn_deriv_F_plus`'s proof via
  `integrableOn_Ioi_deriv_of_nonpos` at `:389`; the existence of
  `integrableOn_Ioi_deriv_of_nonneg` at mathlib `IntegralEqImproper:755`; the
  three axiom-transcript results.
* **MEASURED:** `D²F₊ > 0` with no sign change on `[0,4]`, so `F₊` is convex
  there; the `F₊ / D¹ / D²` decay table; `deriv F_plus 0 = ω(1)/2 + ω′(1) =
  −0.1141956486` and `deriv F_minus 0 = ω′(1) = −0.1358043514`, both nonzero.
* **JUDGEMENT (mine):** that a second IBP is what "boundary analysis" must mean
  here; that the `omega''` construction is a mechanical mirror; that route 2
  (majorant) should be tried before route 1 (sign lemma); the line estimates.
* **OPEN / NOT established:** **the spec itself, which I never saw** — check 5 is
  inferred and could be the wrong list; convexity is measured on `[0,4]`, not
  proved anywhere and not checked beyond `u=4` (it is not in doubt
  asymptotically, but it is not a theorem); the 100–400 L spread on the
  integrability row is unelaborated, and it is the number the whole estimate
  turns on.

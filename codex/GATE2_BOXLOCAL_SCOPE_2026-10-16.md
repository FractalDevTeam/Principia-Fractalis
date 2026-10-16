# Gate-2 box-local bound: decision brief. The 6.886 ceiling is the `L = 1` threshold, not a limit of the method — and passing it needs no new mathematics.

**Date:** 2026-10-16 (Legion, compute on Acer). **Scoping only, no Lean.**
Decision brief for the strategy call at centre 27/4. Verification:
`codex/gate2_scope_verify.py` + `codex/gate2_cost_verify.py`. Labels FACT / ARITHMETIC / JUDGEMENT / OPEN.

**Headline, and it reframes the call:**

1. **Gate 2 never actually binds.** With true values the Gate-2 quantity peaks
   at **0.347 against a budget of 2** and decays like `~4/t`. The 6.886 ceiling
   is an artifact of using one *constant* where the truth decays.
2. **The ceiling is exactly the `L = 1` threshold** — algebraically, not
   approximately. Passing it requires **no new mathematics and not even new
   constants**: stop hard-coding `L = 1, r = 1/16, Mc_lb = 1/8`. That reaches
   `t = 10` in 40 boxes with theorems that exist today.
3. **The real cost is panel generation, not proof difficulty** (~11.5k lines of
   generated Lean per box), and the real boundary is `t = 13.9883806982`, where
   `Re ξ(1+it)` first vanishes and a positivity march's conclusion becomes
   **false**, not merely unprovable.

---

## 0. What Gate 2 is actually bounding — ARITHMETIC (derived here)

From `2ξ(s) = s(s−1)Λ₀(s) + 1` at `s = 1+it`, with `s(s−1) = −t² + it`:

  `d/dt[2ξ(1+it)] = (−2t + i)·Λ₀ + (−t² + it)·i·Λ₀'`

so `|d/dt 2Re ξ| ≤ √(1+4t²)·|Λ₀| + |t|√(t²+1)·|Λ₀'| ≤ (1+2|t|)B + (t²+|t|)B'`
for any `B ≥ |Λ₀|`, `B' ≥ |Λ₀'|` on the box. Gate 2 wants `|d/dt Re ξ| ≤ L`, so

  **`L(t) = [ (1+2t)·B + (t²+t)·B' ] / 2`.**

With `B = B' = 50/1727` and `L = 1` this is exactly the scaffold's
`50(1+2|t|) + 50(t²+|t|) ≤ 2·1727`. **So the ceiling `|t| ≤ 6.8863` is precisely
where `L(t)` crosses 1** — setting `L = 1` gives `50(t²+3t+1) = 3454`, the
identical inequality. Verified: `L(7) = 1.0278`, just over.

**This is the whole finding.** 6.886 is not a limit of the bound, the method, or
the mathematics. It is the point at which a hard-coded constant stops being
true.

## 1. What a box-local bound would require — FACT (read in source) + JUDGEMENT

**Two objects, not one.** `‖Λ₀(1+it)‖` and `‖deriv completedRiemannZeta₀ (1+it)‖`
bounded separately over the box's `t`-range. The present route uses a single
constant for both, and that is the defect:

| t | `\|Λ₀\|` | `\|Λ₀'\|` | 50/1727 loose on Λ₀ | loose on Λ₀' |
|---|---|---|---|---|
| 7 | 1.42e−2 | 1.84e−3 | 2.0× | 15.7× |
| 10 | 9.22e−3 | 1.40e−3 | 3.1× | 20.8× |
| 12 | 6.81e−3 | 1.02e−3 | 4.3× | 28.3× |
| 14 | 5.09e−3 | 7.11e−4 | 5.7× | 40.7× |

**Why Λ₀' is so much looser, and this is the mechanism.**
`Lambda0UltraTightBoundsMellin_2026_10_14.lean` §3 is titled *"derivative
version via Cauchy"*: `lambda0_prime_abs_le_fifty_over_1727` is obtained by
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` at **radius 1** from the
strip bound `lambda0_abs_le_fifty_over_1727_strip (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2)`
— which is uniform in `t` (`t` is a free variable with no hypothesis). So `Λ₀'`
inherits `Λ₀`'s constant wholesale, while the truth decays one extra power
(`|Λ₀| ~ 1/t²`, `|Λ₀'| ~ 2/t³` — confirmed: at `t=14`, `1/t² = 5.10e−3` vs true
`5.09e−3`, and `2/t³ = 7.29e−4` vs true `7.11e−4`).

**The method difference.** The uniform bound takes absolute values inside the
Mellin integral, discarding the oscillatory factor `x^{it/2}`. Decay *is* that
oscillation, so a decaying bound must integrate by parts — which is exactly
what this project's L4 identity already does.

**And here is the structural catch.** `lambda0_edge_ibp_identity` is stated at
**σ = 1 only**. Cauchy needs the bound on a **disc** around `1+it`, i.e. on a
strip. So the existing L4 cannot be dropped in; it would have to be re-derived
σ-parametrically. **JUDGEMENT:** this is the single fact that separates "cheap"
from "weeks", and it is why §2 is tiered.

## 2. Tightening or new mathematics? — three tiers, and the answer is "mostly neither"

### Tier 1 — pure instantiation. NO new mathematics, no new constants. ARITHMETIC

Let `L` grow and shrink `r` to compensate, with `Mc_lb ≤ Re ξ(centre)`:

| centre | `Re ξ` | `L` (uniform) | attainable `r` | ≈ 1/r |
|---|---|---|---|---|
| 7 | 0.150981 | 1.0278 | 0.1175 | 8.5 |
| 8 | 0.101916 | 1.2884 | 0.0633 | 15.8 |
| 10 | 0.036811 | 1.8964 | 0.0155 | 64 |
| 12 | 0.008194 | 2.6202 | 0.0025 | 400 |
| 13 | 0.002509 | 3.0255 | 0.00066 | 1507 |

(using `Mc_lb = 0.8·Re ξ`). The Gate-2 lemma in the scaffold is already a
general inequality; only the *instantiation* fixes `L = 1`. **Nothing needs to
be proved to march past 6.886.**

### Tier 2 — tightening (same proof, sharper constants). LIMITED

Widening the Cauchy radius from `ρ = 1` improves `B'` by a factor `ρ`, but
requires the strip bound on a wider `σ`-range (presently `σ ∈ [0,2]`, so `ρ = 1`
is maximal from `σ = 1`). Extending to `σ ∈ [−1,3]` buys **2× at best**, against
the 15–41× available. **Not worth doing on its own.**

### Tier 3 — genuinely new mathematics, bounded in scope. WEEKS

A `t`-decaying **strip** bound `‖Λ₀(σ+it)‖ ≤ B(t)` on `σ ∈ [1−ρ, 1+ρ]`, after
which the *identical* Cauchy step yields `‖Λ₀'(1+it)‖ ≤ sup_disc B / ρ`. This is
L4's construction re-run σ-parametrically: the `ibp_phase` lemma generalises,
but `F_plus u = e^{u/2}ω(e^u)` becomes `e^{σu/2}ω(e^u)` and every
integrability/decay lemma needs re-proving with σ-dependence. **It is a re-run
of an existing idea, not a new idea** — L4 was 19 declarations and a lane of
work.

## 3. Cost, and what could fail

**Tier 1: hours to ~2 days of proof work — but the binding cost is panel
generation.** The landed c=51/8 box was 3280 lines plus 8219 lines of generated
panels ≈ **11.5k lines of Lean per box**. That, not proof difficulty, prices the
march:

| reach | Tier 1 boxes | Tier 3 boxes | Tier 1 ≈ lines |
|---|---|---|---|
| t = 8 | 7 | 2 | ~80k |
| t = 10 | 40 | 6 | ~460k |
| t = 12 | 215 | 25 | ~2.5M |
| t = 13 | 616 | 58 | ~7.1M |
| t = 13.9 | 3389 | 247 | ~39M |

**Tier 3: weeks**, and it buys a **~13× box-count reduction**, not new reach.

**What could fail — OPEN, three things, in order of likelihood:**

1. **Gate 1 degrades as Gate 2 eases.** My c=13/2 brief already shows the
   enclosure budget tightening with `c`; at `t = 10` the required `Mc_lb ≈ 0.03`
   leaves a quarter of the room `1/8` did, and the panel enclosure width *grows*
   with `t` because `cos(cu/2)` oscillates faster. **Gate 1 becomes the binding
   constraint, exactly where Gate 2 stops being one.** This is the most likely
   failure and it is not addressed by any Gate-2 work.
2. **Tier 3's σ-parametric IBP may not close uniformly** as `σ → 0`, where ζ's
   behaviour worsens; the Cauchy radius would have to shrink, handing back the
   gain through the `1/ρ`.
3. **Box count diverges at the endpoint** in both scenarios: `Re ξ → 0` forces
   `r → 0`. The table above is finite only because it stops short of 13.9884.

## 4. How far does it buy? — the question has the wrong shape. ARITHMETIC

Not "another 3 boxes, or 10, or to 13". **Gate 2 ceases to bind at all.** With
true values:

| t | `(1+2t)\|Λ₀\|` | `(t²+t)\|Λ₀'\|` | total | ≤ 2? |
|---|---|---|---|---|
| 6.886 | 0.2120 | 0.0997 | 0.3117 | yes |
| 10 | 0.1936 | 0.1535 | **0.3471** (peak) | yes |
| 13.99 | 0.1477 | 0.1493 | 0.2970 | yes |
| 20 | 0.1024 | 0.1049 | 0.2073 | yes |
| 50 | 0.0404 | 0.0408 | 0.0812 | yes |

Both terms are `O(1/t)` — `(1+2t)/t² → 0` and `(t²+t)·2/t³ → 0`. Peak **0.347
against a budget of 2**, i.e. a factor **5.8 of headroom at the worst point.**

**The hard boundary is elsewhere and is genuine.** `Re ξ(1+it)` first vanishes
at `t = 13.9883806982` (this project's established value, independently
reproduced here):

```
Re xi(1+i·13.9    ) = +1.378e-04
Re xi(1+i·13.9883) = +1.196e-07
Re xi(1+i·13.99   ) = -2.397e-06
Re xi(1+i·14.1    ) = -1.550e-04
```

Past it a positivity march's **conclusion is false**, not merely unprovable. So
`t < 13.9884` caps *every* version of this march, Tier 3 included.

**OPEN, and it should be settled before any Tier-3 spend — JUDGEMENT.** The
reduction `rh_below_15_conditional` targets `[0,1]×[−15,15]` via three
right-edge sign facts `R1 ∧ R2 ∧ R3`. If `R1` is right-edge *positivity*, it
cannot reach 15 by construction, because the sign changes at 13.9884 (and this
project recorded 13 sign changes in `[0,60]`). **Whatever closes the gap from
13.9884 to 15, it is not more positivity boxes.** I have not re-read the
R1/R2/R3 statements to confirm which is which, and that check costs an hour and
should precede committing weeks.

## 5. Recommendation

**Do Tier 1 at the 27/4 decision point. Do not build Tier 3 yet.**

* Tier 1 is hours, needs no new theory, and immediately demonstrates that the
  6.886 "ceiling" was never real — which is worth knowing regardless of what is
  decided next.
* It also re-poses the strategy call correctly. The question is not "can we pass
  6.886" (yes, free) but **"is `t ≈ 10` for ~40 boxes / ~460k generated lines
  worth having, and does the target actually need `t > 13.9884`?"**
* Tier 3's 13× box-count reduction only pays if the answer to the second half is
  that reach beyond `t ≈ 10` matters. Given §4's OPEN item — that positivity
  cannot reach 15 at all — **settle what `R1` needs before spending weeks on a
  13× efficiency gain for a march that may be capped below the target anyway.**

**JUDGEMENT on the shape of the whole thing.** Two ceilings were being
conflated: a hard-coded constant (6.886, free to remove) and a genuine sign
change (13.9884, immovable). The work that matters is at neither — it is Gate
1's enclosure budget in between, which is where my c=13/2 brief already found
the residue lever.

---

## Label summary

* **FACT (read in source):** `lambda0_abs_le_fifty_over_1727_strip` is uniform
  in `t` over `σ ∈ [0,2]`; `lambda0_prime_abs_le_fifty_over_1727` is obtained by
  Cauchy at radius 1 (§3, "derivative version via Cauchy"); `L4` /
  `lambda0_edge_ibp_identity` is stated at `σ = 1` only; the landed c=51/8 box
  is 3280 + 8219 lines.
* **ARITHMETIC (computed here):** the derivative decomposition and
  `L(t) = [(1+2t)B + (t²+t)B']/2`; that `L = 1` reproduces the scaffold's
  inequality exactly and `L(7) = 1.0278`; the looseness table (2.0–5.7× on Λ₀,
  15.7–40.7× on Λ₀'); the asymptotic checks `|Λ₀| ~ 1/t²`, `|Λ₀'| ~ 2/t³`; the
  Gate-2 true-value table peaking at 0.347; the Tier-1/Tier-3 box counts; the
  sign-change bracketing of 13.9883806982.
* **JUDGEMENT (mine):** that the σ=1 restriction of L4 is what separates cheap
  from weeks; that Gate 1 becomes binding exactly where Gate 2 stops being; the
  tiering; the recommendation to do Tier 1 and defer Tier 3; that the R1
  question should be settled first.
* **NOT established:** that a σ-parametric L4 closes (Tier 3 is scoped, not
  attempted); which of `R1/R2/R3` is the positivity fact; the actual certified
  panel widths at `t > 6.5` (Gate-1 side, flagged as the likely real
  obstruction).

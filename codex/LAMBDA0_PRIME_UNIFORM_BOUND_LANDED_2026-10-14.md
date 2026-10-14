# Λ₀' uniform modulus bound — LANDED, 2026-10-14

Author: Pablo Cohen + Claude Opus 4.7 (1M context). Second major piece of
Rank-1.5 pilot producer landed kernel-clean.

## What landed

`PF/Analytic/Lambda0PrimeUniformBound_2026_10_14.lean` (164 L). **6 kernel-clean
theorems**, every one `[propext, Classical.choice, Quot.sound]`. Zero project
axioms. No `sorry`, `native_decide`, `axiom`, or `Prop := True`. Build 8.7 s.

### Theorems

**Exponent real parts, σ-parameterised (§0):**
- `re_exp_a_sigma σ t : ((⟨σ, t⟩ : ℂ) / 2 - 1).re = σ/2 - 1`
- `re_exp_b_sigma σ t : ((1 - (⟨σ, t⟩ : ℂ)) / 2 - 1).re = (1-σ)/2 - 1`

**Strip-uniform integrand bound (§1):**
- `norm_integrand_bound_strip` — same bound as the σ=1 case but on σ ∈ [0, 2],
  valid because both exponents remain ≤ 0 on the strip.

**Strip-uniform Λ₀ bound (§2):**
- `lambda0_abs_uniform_strip σ t (hσ0 hσ2) : ‖Λ₀(⟨σ, t⟩)‖ ≤ 2·exp(-π)/(π·(1-exp(-π)))`
- `lambda0_abs_le_two_thirds_strip σ t (hσ0 hσ2) : ‖Λ₀(⟨σ, t⟩)‖ ≤ 2/3`

**Cauchy derivative bound (§3) — THE RESULT:**
- **`lambda0_prime_abs_le_two_thirds (t : ℝ) :
    ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2/3`**

The Cauchy formula on the disk of radius 1 around `1+it` is used via mathlib's
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. The disk lies entirely in
the strip Re(z) ∈ [0, 2] (since `|Re(z) - 1| ≤ ‖z - (1+it)‖ = 1`), so the
strip-uniform bound applies on the whole sphere, giving
`‖deriv Λ₀ (1+it)‖ ≤ (2/3) / 1 = 2/3`.

## What this does NOT yet close

The pilot's `hbound : ∀ x ∈ Icc (9/20) (11/20), |deriv edgeRe x| ≤ 1/10`.

The remaining chain, deferred to a follow-up session:
1. **Chain rule.** `deriv edgeRe t = -(deriv riemannXiEntire (⟨1,t⟩)).im` via
   `Complex.reCLM.hasFDerivAt.comp_hasDerivAt` composition with the real-to-
   complex line map.
2. **ξ product rule.** `deriv riemannXiEntire (⟨1,t⟩) =
      ((2s-1)·Λ₀(s) + s(s-1)·Λ₀'(s)) / 2` at `s = 1+it`, via mathlib's
   `HasDerivAt.mul` on the definition `ξ(s) = (s(s-1)·Λ₀(s) + 1)/2`.
3. **Triangle-inequality bounds on `|2s-1|` and `|s(s-1)|`** at `s = 1+it`,
   `|t| ≤ 11/20`. By triangle:
   - `|2s-1| = |1+2it| ≤ 1 + 2·|t| ≤ 21/10`
   - `|s(s-1)| ≤ |s|·|s-1| ≤ (1+|t|)·|t| ≤ 341/400 ≤ 1`
4. **Final combination:** `|deriv edgeRe x| ≤ |ξ'(1+ix)|
      ≤ (|2s-1|·‖Λ₀‖ + |s(s-1)|·‖Λ₀'‖) / 2 ≤ ((21/10)·(2/3) + 1·(2/3))/2 = 31/30`.

**Observation:** the pilot box's `L = 1/10` is NOT reachable with the loose
`‖Λ₀‖, ‖Λ₀'‖ ≤ 2/3` bounds — the chain gives `≤ 31/30 ≈ 1.03`. Two options:

**Option A** (preferred — session scope): adjust the pilot box params to
`L = 2, r = 1/20, Mc_lb = 1/4`. Then `L·r = 1/10 < 1/4 ✓` and the chain
`|deriv edgeRe x| ≤ 31/30 ≤ 2` closes with margin. New pilot file
`PilotBoxes/R1_c0_5_r0_05_L_2_2026_10_14.lean`.

**Option B** (tighter — multiple sessions): refine `‖Λ₀‖ ≤ 2/3` to
`‖Λ₀‖ ≤ 2/21 ≈ 0.095` via sharper exp(-π) ≤ 1/20 numerics
(`Real.exp_one_near_10` chain). Then `|deriv edgeRe x| ≤ 2.1·(2/21) + (2/21) ≈ 0.3`,
which closes `L = 1/2` or similar. Still not `L = 1/10`.

**Option C** (tightest — many sessions): tight Λ₀ integral evaluation
(`exp(-π) < 1/23` numerics) + evaluate Λ₀' integral directly via differentiated
Mellin + log-u bound. Closes `L = 1/10` for small boxes.

## Why execute Λ₀' this session but not the full chain

Session budget hit three nontrivial Lean API gaps on the chain-rule side:
- `Complex.abs` deprecated → use `‖·‖`
- `HasDerivAt.real_of_complex` is for `ℂ → ℂ` restricted to reals, not `ℝ → ℂ`
- `HasDerivAt.mul` returns `h.val·k' + h'·k.val`, mathlib order differs from mine
- `sq_le_sq'` is not an iff — use `nlinarith` with `abs_le`

Each is tractable; collectively they overran the session budget. The Λ₀'
Cauchy proof landed clean. The chain rule is a dedicated follow-up.

## Rank-1.5 progress record

| step | state | this session |
|------|-------|--------------|
| Lean consumer (`R{1,2,3}_box_centered_of_*`) | DONE | 2026-10-13 |
| Pilot box emitter (Python) | DONE | 2026-10-13 |
| Three pilot box files | DONE | 2026-10-13 |
| `‖Λ₀(1+it)‖ ≤ 2/3` uniform | DONE | 2026-10-14 earlier |
| First producer-side hypothesis (`hvalue_lb`) | DONE | 2026-10-14 earlier |
| **`‖Λ₀(z)‖ ≤ 2/3` on strip σ ∈ [0, 2]** | **DONE** | **this cycle** |
| **`‖deriv Λ₀ (1+it)‖ ≤ 2/3` (Cauchy)** | **DONE** | **this cycle** |
| Chain rule `deriv edgeRe = …` | open | next session |
| ξ product rule `deriv ξ = …` | open | next session |
| `|deriv edgeRe x| ≤ L` for pilot | open | next session |
| First full pilot box closed end-to-end | open | after above |

Pilot producer is now **2 of 3 producer-side pieces done**. Remaining piece
is the chain rule plus triangle inequalities, maybe one more focused session.

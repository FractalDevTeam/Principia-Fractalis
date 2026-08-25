# PRINCIPIA FRACTALIS — RH-BELOW-15 TOTAL-COUNT RESIDUAL

**Date:** 2026-08-24
**HEAD:** local `406eaef8` (r323) + `<r324>` — see git report below.
**Companion to:** `codex/RH_FINITE_HEIGHT_FEASIBILITY_2026-08-24.md`
**Deliverable:** the focused decomposition mandated by the post-r324 directive.

The question this document answers:

> **Given r324 (`∃ t ∈ (1, 15), Complex.riemannZeta ⟨1/2, t⟩ = 0`), what is the smallest precise theorem which, combined with r324, would prove literal finite-height RH below height 15?**

Target conclusion (literal, external-standard):

```lean
∀ s : ℂ,
    riemannZeta s = 0 →
    0 < s.im → s.im < 15 →
    0 < s.re → s.re < 1 →       -- nontrivial-zero convention
    s.re = 1/2
```

Non-negotiables (per DIRECTIVE Part XIII):
- No project axioms; no `sorry`; no `native_decide`.
- No use of the α-skeleton, I9, r128 StructuralLaws, H_3, T3 spectrum.
- No mpmath / empirical / database inputs accepted as proof.
- No assumed values like "first ζ zero ≈ 14.1347".

---

## 1. Current PF architecture (after r324)

| Piece | Status |
|---|---|
| r120 `positiveOnLineZetaZeroOrdinatesNonempty` : `∃ t > 0, ζ(1/2 + it) = 0` | PROVED |
| r280 `{t > 0 : ζ(1/2 + it) = 0}.Countable` | PROVED |
| r315 `Xi_15_pos : 0 < Xi 15` | PROVED |
| r323 `riemannZeta ⟨1/2, 15⟩ ≠ 0` (specific point) + generic `Xi ≠ 0 → ζ ≠ 0` on the line | PROVED |
| r324 `∃ t ∈ (1, 15), ζ(1/2 + it) = 0` | PROVED |
| Finite-height RH below 15 | NOT PROVED — this document scopes what is missing |

## 2. Sufficient architecture for finite-height RH below 15

To conclude "every nontrivial ζ zero with `0 < Im s < 15` lies on `Re s = 1/2`", the minimal architecture (with r324 in hand) is:

**A. ≥ 1 critical-line ζ zero with `0 < Im s < 15`.** ← r324 provides this.

**B. EXACT TOTAL COUNT** of nontrivial ζ zeros with `0 < Im s < 15` in the critical strip `0 < Re s < 1`, counted with multiplicity, equal to some finite N.

**C. ≥ N critical-line zeros in the same height range.** (May follow directly from r120/r324/etc., depending on N.)

If A + B + C hold with the counts matching, the ON-LINE zeros exhaust the TOTAL, hence every off-line zero would be a duplicate, contradiction, hence no off-line zero.

**Load-bearing residual: B — the EXACT TOTAL COUNT.**

## 3. r280 is NOT a substitute for B

The prior feasibility document previously suggested r280 (countability) could bridge to a finite count. That was too weak. Countability gives at most `Nat.card ≤ ℵ₀`; it does NOT give a specific finite value or a bound.

Once an exact total finite count N is available (from B), r280 is redundant. Before it is available, r280 does not help.

**r280 remains valuable** as a structural result about the shape of the zero set. It does not solve the counting problem.

## 4. Three candidate counting routes

### Route CR-A — Meromorphic ζ contour count via argument principle

Contour: boundary of a rectangle avoiding the pole `s = 1` and all ζ zeros. E.g., `[ε, 1 - ε] × [0, 15]` (offset from `Re = 0` and `Re = 1` since ζ has no zeros there per classical results, but formalized: only zero-free at `Re s ≥ 1` for `s ≠ 1` per mathlib presently; `Re s = 0` non-vanishing is nontrivial).

Argument principle: `(1 / (2πi)) ∮_γ ζ'/ζ = (zero count in γ interior)` (since ζ has no poles inside the offset rectangle).

**Required (all simultaneously):**
- General meromorphic argument principle in mathlib — ABSENT.
- ζ'/ζ integrability along the contour — needs certified nonvanishing at all contour points.
- Nonvanishing of ζ along the entire contour — nontrivial at `Re = ε` for small ε.
- Winding-number computation certified to integer precision.
- Multiplicity handling.
- Boundary handling `Im s = 15`: r323's `riemannZeta_ne_zero_at_critical_15` handles the top-boundary intersection with the critical line, but not the corners `⟨ε, 15⟩` or `⟨1-ε, 15⟩`.

**Estimate:** cannot be estimated as a bounded PF task without scoping each of the seven pieces above. Not attempted.

### Route CR-B — Completed-zeta contour count with pole bookkeeping

`completedRiemannZeta s = π^(-s/2) Γ(s/2) ζ(s)` has poles at `s = 0` and `s = 1` (from the two rational-term subtraction in mathlib's definition). Contour avoiding both poles.

**Advantage over CR-A:** functional equation `completedRiemannZeta s = completedRiemannZeta (1 - s)` in mathlib (`completedRiemannZeta_one_sub`) may enable half-plane arguments.

**Same requirements** as CR-A plus pole bookkeeping. Not attempted.

### Route CR-C — Entire-function `completedRiemannZeta₀` contour count

`completedRiemannZeta₀` is entire (in mathlib), defined as `completedRiemannZeta s + 1/s + 1/(1-s)`. Its zeros need to be related to nontrivial ζ zeros.

**Critical verification needed BEFORE this route can be considered:**
- Do zeros of `completedRiemannZeta₀` in the strip `0 < Re s < 1` correspond EXACTLY to nontrivial ζ zeros? On the critical line specifically?
- At `s = 1/2 + it` for `t ≠ 0`, `1/s` and `1/(1-s)` are conjugates (since `1 - (1/2 + it) = 1/2 - it = conj(1/2 + it)`), so `1/s + 1/(1-s)` is REAL and equal to `2 · Re(1/s)`. Hence adding it to `completedRiemannZeta s` shifts the real part but not the imaginary part. On the critical line, `completedRiemannZeta ⟨1/2, t⟩` is real (Xi_im_eq_zero), so its zero locus on the critical line differs from `completedRiemannZeta₀`'s zero locus by the specific real shift `1/(1/2 + it) + 1/(1/2 - it) = (1/2 - it + 1/2 + it) / ((1/2)² + t²) = 1 / (1/4 + t²)`. This is a NONZERO real number for every t, so **`completedRiemannZeta` and `completedRiemannZeta₀` have DIFFERENT zero sets on the critical line.**

So CR-C is NOT directly viable — the entire `completedRiemannZeta₀` does not share zeros with nontrivial ζ on the critical line.

Alternative: some other entire reformulation whose zeros exactly correspond. This does not appear to exist in mathlib as a named theorem.

**Verdict:** CR-C rejected as a shortcut. There is no entire reformulation currently available whose zeros equal nontrivial ζ zeros. The "entire Xi function" of classical analytic number theory (`ξ(s) := (1/2) s (s-1) π^(-s/2) Γ(s/2) ζ(s)`, entire, with zeros exactly at nontrivial ζ zeros) is NOT in mathlib as a named object.

## 5. Comparison table

| Route | Available? | Blocker(s) |
|---|---|---|
| CR-A (raw ζ) | NO | argument principle absent; boundary nonvanishing not certified |
| CR-B (completedRiemannZeta) | NO | same as CR-A + pole bookkeeping |
| CR-C (completedRiemannZeta₀) | NO | zeros do not match nontrivial ζ zeros on critical line |

## 6. Additional missing pieces even IF a route were unlocked

Given any of CR-A/B/C infrastructure, the following pieces would still be required for a certified finite count:

1. **Certified boundary nonvanishing.** Even if `Re s = 1` is zero-free classically (Wiener-Ikehara-adjacent), this needs formal proof. Mathlib does not have this yet in a form that admits offset contours.
2. **Certified argument variation.** Number of `2π`-jumps of `arg(ζ(s))` along the contour, certified to integer precision. Requires certified numerical evaluation of ζ (or ζ'/ζ) at many contour points.
3. **Rectangle-corner behavior.** Certified nonvanishing at the four corners and along all four sides.
4. **Multiplicity.** Even if a zero count is obtained, ruling out higher multiplicity requires additional analytic input (e.g., that all first-few ζ zeros are simple — classical fact, formalization status unknown).

## 7. Nearest existing theorem to unlock the residual

The single most useful step toward B, given current mathlib state, is a **certified numerical evaluation of `Complex.riemannZeta` at prescribed points**, along the lines of the r120 / r315 pipeline extended to a rectangular contour.

But this is a certified-numerics enterprise (per r120's scale: 14 segments, 474 panels, 165 kernel-decide bricks — for ONE integral). Extending to a closed contour with multiple sides, with the argument principle infrastructure additionally in place, is significantly larger than r120's project scope. Not bounded.

## 8. Verdict per DIRECTIVE Part XII

**If the smallest correct residual requires general argument principle + winding number + substantial certified complex ζ numerics, freeze finite-height RH there.**

That is exactly the situation. The B residual (EXACT TOTAL COUNT of nontrivial ζ zeros with `0 < Im s < 15`) requires:

- A general argument-principle / winding-number infrastructure that mathlib does not currently provide.
- A specialized certified ζ contour computation that PF does not currently have.
- The equivalence between mathlib's `completedRiemannZeta₀` and the classical entire ξ is FALSE on the critical line (per §4's arithmetic on `1/s + 1/(1-s)`); so the "shortcut" via an entire reformulation is closed.

**FROZEN.** Finite-height RH below 15 is not achievable as a bounded PF landing.

## 9. What HAS been achieved

The r120 → r315 → r323 → r324 chain established:

- ≥ 1 literal `Complex.riemannZeta` zero on the critical line with `0 < Im s < 15` (r324, tightened from r120).
- `Complex.riemannZeta ⟨1/2, 15⟩ ≠ 0` (r323).
- Positive on-line ζ ordinates form a countable set (r280).
- Full RH conditionally reduced to Hardy 1914 + HP-program (r255).

These are real literal-ζ results. The finite-height statement remains open pending the counting infrastructure.

## 10. Recommendation

**NO NEW LANDING RECOMMENDED at this time.** Per DIRECTIVE Part XII, freeze finite-height RH here.

If further work is authorized on this axis, the smallest genuinely-productive next step is a **certified boundary-nonvanishing lemma** — e.g., `∀ σ ∈ [ε, 1-ε], riemannZeta ⟨σ, 15⟩ ≠ 0` for some explicit ε — which would contribute one side of the rectangular contour without requiring the full argument-principle apparatus. But this itself would require substantial extension of r120/r315-style quadrature machinery, and would not close the residual alone.

---

## Summary

**r324 landed:** literal `∃ t ∈ (1, 15), Complex.riemannZeta ⟨1/2, t⟩ = 0`, a rigorous tightening of r120's on-line ζ-zero existence using r315 as sharper right endpoint. Kernel-clean.

**Load-bearing residual for finite-height RH below 15:** EXACT TOTAL COUNT of nontrivial ζ zeros with `0 < Im s < 15`, counted with multiplicity, in the critical strip.

**None of three candidate counting routes** (raw ζ, completedRiemannZeta, completedRiemannZeta₀) is currently viable:
- Raw ζ: argument principle absent from mathlib.
- CompletedRiemannZeta: same + pole bookkeeping.
- completedRiemannZeta₀: zeros do NOT match nontrivial ζ zeros on the critical line — shortcut closed by direct computation of `1/s + 1/(1-s)`.

**Additional missing pieces:** certified boundary nonvanishing, certified argument variation to integer precision, corner behavior, multiplicity.

**Verdict:** finite-height RH below 15 is FROZEN. Not a bounded PF landing.

**What HAS been achieved on this axis:** r120 existence, r280 countability, r315 Xi(15) positivity, r323 point-wise ζ nonvanishing at t=15, r324 literal ζ zero in `(1, 15)` — a coherent stack of literal `Complex.riemannZeta` results, none of which discharges finite-height RH.

**Not implementing without your authorization.** Per DIRECTIVE Part XII: STOP.

---

**End of residual scoping.**

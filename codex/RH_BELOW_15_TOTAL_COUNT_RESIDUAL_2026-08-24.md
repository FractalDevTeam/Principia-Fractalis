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

Contour: boundary of a rectangle enclosing the nontrivial-zero region and avoiding the pole `s = 1` and all ζ zeros.

**Update (2026-08-25, this section revised):** mathlib provides
`riemannZeta_ne_zero_of_one_le_re : 1 ≤ s.re → riemannZeta s ≠ 0`
(`Mathlib/NumberTheory/LSeries/Nonvanishing.lean:407`, Hadamard /
de la Vallée-Poussin, ≈ Prime Number Theorem prerequisite).  This is
UNCONDITIONAL and covers the entire closed half-plane `Re s ≥ 1`,
including the boundary line `Re s = 1` and the pole `s = 1` itself
(mathlib's junk value at `s = 1` happens to be nonzero).

**Clarification (2026-08-25).**  `riemannZeta_ne_zero_of_one_le_re`
gives a POINTWISE-TOTALIZED nonzero value for mathlib's `riemannZeta`
at every `s` with `Re s ≥ 1`, INCLUDING `s = 1`.  This does NOT mean
the meromorphic ζ-function is HOLOMORPHIC at `s = 1` — classically
and analytically, `s = 1` remains a pole.  A meromorphic
argument-principle contour along or through `Re s = 1` cannot simply
pass through `s = 1`; the pole would contribute a residue.

This makes the CR-D route (r325's `riemannXiEntire`) even more
valuable: `riemannXiEntire` is genuinely entire (no pole at 1), so
no pole bookkeeping is needed if the count is done via the classical
entire ξ.

Consequence: on the boundary of the rectangle `[0, 1] × [0, 15]`, the
right side `Re s = 1, Im s ∈ [0, 15]` is **already certified nonvanishing**
by mathlib. No ε-offset from `Re s = 1` is required.

Argument principle: `(1 / (2πi)) ∮_γ ζ'/ζ = (zero count in γ interior)`,
where γ can be taken as the boundary of `[0, 1] × [0, 15]` (with the
pole at s = 1 lying ON the boundary corner, requiring careful contour
choice — e.g., a small semicircular detour or an ε-offset from the
`Im s = 0` axis, since `Re s ≤ 0` needs the functional equation to
derive zero-freeness).

**Required (all simultaneously), with mathlib coverage marked:**
- General meromorphic argument principle in mathlib — **ABSENT**.
- `Re s = 1` side of contour zero-free — **PRESENT** via
  `riemannZeta_ne_zero_of_one_le_re`.
- `Re s = 0` side of contour: needs functional equation + Re ≥ 1
  result — **derivable in principle from mathlib's `riemannZeta_one_sub`
  + `riemannZeta_ne_zero_of_one_le_re`, but not landed as a named
  theorem.**
- `Im s = 0` bottom side: nontrivial zeros come in complex-conjugate
  pairs (so real-line zeros in `(0, 1)` would contradict; but this
  is not obviously formalized as `∀ σ ∈ (0, 1), riemannZeta σ ≠ 0`).
- `Im s = 15` top side: r323 handles the critical-line point
  `⟨1/2, 15⟩`; nonvanishing at ALL `⟨σ, 15⟩` for `σ ∈ (0, 1)` is
  NOT formalized.
- Winding-number computation certified to integer precision — ABSENT.
- Multiplicity handling — ABSENT.

**Net status after mathlib discovery.** The right side of the contour is
free; the left side is derivable via functional equation but unlanded;
the top and bottom sides plus the argument-principle apparatus remain
absent. Not attempted.

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

**Verdict (unchanged):** CR-C rejected as a shortcut. `completedRiemannZeta₀` itself is entire but has the wrong zero set.

### Route CR-D — Classical entire Riemann ξ (r325, landed 2026-08-25)

`riemannXiEntire s := (s (s − 1) · completedRiemannZeta₀ s + 1) / 2` (r325,
`PF/Analytic/RiemannXiEntire_r325.lean`).  Uses the polynomial correction
dictated by `completedRiemannZeta_eq : Λ = Λ₀ − 1/s − 1/(1-s)`:
multiplying `Λ` by `s (s − 1)` collapses the two pole contributions to `+1`
exactly (`-s(s-1)/s = 1-s` and `-s(s-1)/(1-s) = s`, summing to `1`).

Kernel-proved endpoints (all `[propext, Classical.choice, Quot.sound]` only):
- `differentiable_riemannXiEntire : Differentiable ℂ riemannXiEntire` — ENTIRE globally.
- `riemannXiEntire_eq_completed {s} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
   riemannXiEntire s = s (s − 1) · completedRiemannZeta s / 2` — off-pole factorization.
- `riemannXiEntire_eq_zero_iff_completedRiemannZeta_eq_zero {s} (hs0 hs1) :
   riemannXiEntire s = 0 ↔ completedRiemannZeta s = 0` — off-pole zero equivalence.
- `riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip {s}
   (hre0 : 0 < s.re) (hre1 : s.re < 1) :
   riemannXiEntire s = 0 ↔ riemannZeta s = 0` — **THE HEADLINE**:
   zeros of `riemannXiEntire` in the open critical strip are EXACTLY
   the zeros of literal `Complex.riemannZeta`.

**Verdict for CR-D:** the correct counting object now exists in the corpus.
An argument-principle-based zero count for `riemannXiEntire` in the
rectangle `[0, 1] × [0, 15]` would count exactly the nontrivial ζ zeros
in that region — no pole bookkeeping needed, no wrong-zero-set problem.
Still absent: the argument-principle apparatus itself, certified
boundary nonvanishing of `riemannXiEntire`, certified winding number,
multiplicity (naturally counted by the argument principle).

## 5. Comparison table

| Route | Available? | Blocker(s) |
|---|---|---|
| CR-A (raw ζ, meromorphic) | NO | argument principle absent; **s = 1 is a pole of the meromorphic ζ** (mathlib's `riemannZeta_ne_zero_of_one_le_re` is a pointwise-totalized-value statement, not a holomorphic-at-1 statement); pole bookkeeping required; boundary nonvanishing partial per §4 |
| CR-B (completedRiemannZeta, meromorphic) | NO | same as CR-A + poles at BOTH `s = 0` and `s = 1` |
| CR-C (completedRiemannZeta₀, entire) | NO | zeros do not match nontrivial ζ zeros on the critical line (`1/s + 1/(1-s) = 1/(1/4 + t²) ≠ 0`) |
| **CR-D (riemannXiEntire, entire, r325)** | **PARTIALLY — object landed** | **Zero-set equivalence with `riemannZeta` in the open critical strip PROVED (r325). Argument-principle apparatus + boundary nonvanishing + winding number certification still absent. This is the correct counting object once those pieces exist.** |

## 6. Additional missing pieces even IF a route were unlocked

Given any of CR-A/B/C infrastructure, the following pieces would still be required for a certified finite count:

1. **Certified boundary nonvanishing.** Even if `Re s = 1` is zero-free classically (Wiener-Ikehara-adjacent), this needs formal proof. Mathlib does not have this yet in a form that admits offset contours.
2. **Certified argument variation.** Number of `2π`-jumps of `arg(ζ(s))` along the contour, certified to integer precision. Requires certified numerical evaluation of ζ (or ζ'/ζ) at many contour points.
3. **Rectangle-corner behavior.** Certified nonvanishing at the four corners and along all four sides.
4. **Multiplicity.** Even if a zero count is obtained, ruling out higher multiplicity requires additional analytic input (e.g., that all first-few ζ zeros are simple — classical fact, formalization status unknown).

## 7. Nearest existing theorem to unlock the residual

The single most useful step toward B, given current mathlib state, is a **certified numerical evaluation of `Complex.riemannZeta` at prescribed points**, along the lines of the r120 / r315 pipeline extended to a rectangular contour.

But this is a certified-numerics enterprise (per r120's scale: 14 segments, 474 panels, 165 kernel-decide bricks — for ONE integral). Extending to a closed contour with multiple sides, with the argument principle infrastructure additionally in place, is significantly larger than r120's project scope. Not bounded.

### Smaller intermediate landings potentially available

Given the mathlib `riemannZeta_ne_zero_of_one_le_re` discovery (§4), several small named-theorem landings now become trivially available:

1. `riemannZeta_ne_zero_at_top_right_corner :
   ∀ σ : ℝ, 1 ≤ σ → riemannZeta ⟨σ, 15⟩ ≠ 0` — one-line specialization of
   mathlib's theorem at `Im s = 15`.
2. `riemannZeta_ne_zero_on_re_one_line :
   ∀ t : ℝ, riemannZeta ⟨1, t⟩ ≠ 0` — one-line specialization.
3. A functional-equation-based left-side companion:
   `riemannZeta_ne_zero_of_re_le_zero_and_ne_neg_two_mul_nat_add_one`
   — derivable from `riemannZeta_one_sub` + `riemannZeta_ne_zero_of_one_le_re`
   + Gamma nonvanishing at those points, but requires care around the
   trivial zeros `s = -2, -4, ...`.

None of these individually addresses the counting residual. They are boundary-nonvanishing pieces that would be reusable if a certified contour count were ever attempted.

### Multiplicity — corrected characterization

An earlier version of this document listed "multiplicity handling" as if simplicity of individual zeros might be required. That is imprecise. For an argument-principle-based count, zeros are naturally counted WITH multiplicity. To conclude finite-height RH below 15 by exhaustion, we do NOT need to prove any critical-line zero simple IF:
- total zero multiplicity in the region equals some finite N (from the count);
- at least N certified critical-line zeros exist in the region (from r120/r324/etc.).
Then the on-line zeros exhaust the multiplicity budget and no off-line zero is possible. The correct requirement on the counting apparatus is therefore that it counts multiplicity correctly, not that individual zeros be separately proved simple.

## 8. Verdict per DIRECTIVE Part XII

**If the smallest correct residual requires general argument principle + winding number + substantial certified complex ζ numerics, freeze finite-height RH there.**

That is exactly the situation. The B residual (EXACT TOTAL COUNT of nontrivial ζ zeros with `0 < Im s < 15`) requires:

- A general argument-principle / winding-number infrastructure that mathlib does not currently provide.
- A specialized certified ζ contour computation that PF does not currently have.
- The equivalence between mathlib's `completedRiemannZeta₀` and the classical entire ξ is FALSE on the critical line (per §4's arithmetic on `1/s + 1/(1-s)`); so the "shortcut" via an entire reformulation is closed.

**FROZEN.** Finite-height RH below 15 is not achievable as a bounded PF landing.

## 9. What HAS been achieved

The r120 → r315 → r323 → r324 → r325 chain established:

- ≥ 1 literal `Complex.riemannZeta` zero on the critical line with `0 < Im s < 15` (r324, tightened from r120).
- `Complex.riemannZeta ⟨1/2, 15⟩ ≠ 0` (r323).
- Positive on-line ζ ordinates form a countable set (r280).
- Full RH conditionally reduced to Hardy 1914 + HP-program (r255).
- **The classical entire Riemann ξ exists in PF as `riemannXiEntire` (r325), with its zeros in the open critical strip PROVED equal to the zeros of literal `Complex.riemannZeta`.** No pole bookkeeping needed for any future argument-principle-based count that uses this object.

These are real literal-ζ results. The finite-height statement remains open pending the argument-principle apparatus + certified boundary nonvanishing of `riemannXiEntire`.

## 10. Recommendation

**NO NEW LANDING RECOMMENDED at this time.** Per DIRECTIVE Part XII, freeze finite-height RH here.

**Note added 2026-08-25:** the mathlib `riemannZeta_ne_zero_of_one_le_re` discovery (§4) reduces the number of missing contour sides from four to two (bottom `Im s = 0` and top `Im s = 15`), plus the functional-equation-derived left side (`Re s ≤ 0` for non-trivial-zero points) which is derivable but unlanded.

If further work is authorized on this axis, the smallest genuinely-productive next step is a **certified critical-strip top-side nonvanishing lemma** — `∀ σ ∈ (0, 1), riemannZeta ⟨σ, 15⟩ ≠ 0` — which would contribute the top side of the rectangular contour. This would require certified numerical evaluation of ζ along the top edge for σ ∈ (0, 1), extending r120/r315-style quadrature machinery. Still would not close the residual alone (bottom side + argument principle apparatus remain missing), but would be a real substantive step.

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

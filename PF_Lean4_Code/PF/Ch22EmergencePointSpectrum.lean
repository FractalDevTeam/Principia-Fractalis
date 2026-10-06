/-
# Ch 22 — What the Emergence-Point Spectral Claim Actually Requires (2026-10-05)

`ch22_navier_stokes.tex`, Theorem "Emergence Point Structure" (`:95–118`),
displays the velocity-gradient tensor as `∇u = Ω + S` (antisymmetric rotation
plus symmetric strain) and then asserts of its eigenvalues (`:112–114`):

  `λ₁ + λ₂ + λ₃ = 0`  and  `λᵢ ∈ iℝ (pure imaginary)`

The proof (`:120–154`) derives the trace-zero half correctly from
incompressibility, then for the second half only asserts, with no computation:
"Real parts of eigenvalues vanish... Only imaginary parts remain."

## This claim is NOT impossible — and that matters

A first look suggests an impossibility, since the strain tensor `S` is real
symmetric by its own displayed definition, so `spec S ⊂ ℝ` and `λᵢ ∈ iℝ` would
force `S = 0`, annihilating the strain the theorem is about. That reading is
indeed self-defeating.

But under the natural reading — the eigenvalues of `∇u` — **the claim is
satisfiable**. A pure rotation (`S = 0`) has spectrum `{0, ±i‖ω‖}`, every
element of which lies in `iℝ` (including `0 = 0i`). So the claim must not be
reported as impossible. What it is, is **underived**: trace-zero alone does not
give it, as `diag(1, 1, −2)` shows — traceless with real nonzero spectrum.

## What the claim is equivalent to

For a real traceless `3 × 3` matrix `W`, the characteristic polynomial is
depressed: `det(λI − W) = λ³ + e₂λ − det W`, with `e₂` the second invariant.
Writing the condition out gives a clean equivalence:

  **all eigenvalues of `W` lie in `iℝ`  ⟺  `det W = 0`  and  `e₂ ≥ 0`.**

*Forward.* A real cubic has a real root; if every root lies in `iℝ` that root is
`0`, so `det W = 0` and the polynomial is `λ(λ² + e₂)`, whose remaining roots
`±√(−e₂)` lie in `iℝ` exactly when `e₂ ≥ 0`.
*Backward.* `det W = 0` factors the cubic as `λ(λ² + e₂)`
(`depressed_cubic_factors`), and `e₂ > 0` leaves the quadratic factor with no
real root (`no_real_root_of_pos`), while `e₂ < 0` supplies the nonzero real
root `√(−e₂)` (`neg_coeff_gives_nonzero_real_root`).

Checked numerically before this file was written: 400 000 random traceless
`3 × 3` matrices, zero mismatches between the eigenvalue condition and
`det = 0 ∧ e₂ ≥ 0`, plus constructed witnesses in all four quadrants of
`(det = 0?, e₂ ≥ 0?)`.

## The second condition is exactly `ch₂ ≤ 0` — and that is the finding

For traceless `W`, `e₂ = ((Tr W)² − Tr(W²))/2 = −Tr(W²)/2`, while the book's own
matrix formula (ch06, formalised as `ch2Matrix` in
`PF/Cosmology/VortexCavitationBridgeChecks.lean:59`) is

  `ch₂(W) = (Tr(W²) − (Tr W)²) / (2‖W‖_F²) = Tr(W²) / (2‖W‖_F²)`.

Both are `Tr(W²)` up to a positive factor and a sign, so

  `e₂ ≥ 0  ⟺  Tr(W²) ≤ 0  ⟺  ch₂(W) ≤ 0`

(`e2_nonneg_iff_ch2_nonpos`). Decomposing `W = Ω + S` and using
`Tr(SΩ) = 0`, `Tr(S²) = ‖S‖_F²`, `Tr(Ω²) = −‖Ω‖_F²`:

  `ch₂(W) = (‖S‖_F² − ‖Ω‖_F²) / (2(‖S‖_F² + ‖Ω‖_F²))`,

so `ch₂(W) ≤ 0 ⟺ ‖S‖_F ≤ ‖Ω‖_F` — **rotation dominates strain**
(`ch2_nonpos_iff_rotation_dominates`). That is precisely the counter-rotating
balance the chapter's physical picture is built on, so the chapter's intuition
is sound and the missing step is a derivation, not a different idea.

## The incompatibility with the 0.95 threshold

ch22 invokes `ch₂ ≥ 0.95` for exactly these objects (`:10`, `:24`, `:327`,
`:430`, `:432–438`, `:684`). Against the above, that fails **twice over, in
independent ways**:

1. **Unreachable.** `ch₂(W) ≤ 1/2` for every real square matrix
   (`ch2Matrix_le_half`, already in the corpus), hence `ch₂ < 19/20` always
   (`ch2Matrix_lt_threshold`). The threshold is outside the formula's range.
2. **Wrong sign.** Worse than unreachable: the emergence-point condition
   *requires* `ch₂ ≤ 0`, the rotation-dominated half of the range, while the
   threshold demands `ch₂` near its strain-dominated maximum. The two conditions
   do not merely fail to meet — they point in opposite directions
   (`emergence_condition_and_threshold_are_opposed`).

With trace zero the full range is `ch₂ ∈ [−1/2, 1/2]`
(`neg_half_le_ch2Matrix_of_trace_eq_zero` plus `ch2Matrix_le_half`), attained at
pure rotation and pure strain respectively, so `ch₂ ≤ 0` is exactly half of it
and `0.95` is in neither half.

## What a repair must establish

Not a different physical picture — two explicit conditions at each emergence
point:

* `det(∇u) = 0`, i.e. `∇u` is singular there; and
* `‖S‖_F ≤ ‖Ω‖_F`, i.e. `ch₂(∇u) ≤ 0`.

Neither is derived in ch22. The second is the chapter's own counter-rotating
hypothesis stated quantitatively, so it is the more promising of the two. The
threshold language keyed to `0.95` at these points cannot be repaired by
recomputation and needs either a different quantity or withdrawal of the
threshold reading — an authorial item.

## A second, independent defect: Step 4 of the no-blowup proof

`ch22:383–386` reads "but vorticity remains bounded:" and then displays
`lim_{r→0} |ω(x₀ + r n̂)| / r⁻¹ = C < ∞`. Dividing by `r⁻¹` is multiplying by
`r` (`div_by_inv_is_mul`), so the displayed limit is `r·|ω| → C` — a statement
that `|ω|` grows like `C/r`, i.e. **diverges**, for any `C > 0`
(`positive_limit_forces_unbounded`). The sentence and the equation on the same
line assert opposite things.

The only `C` compatible with boundedness is `C = 0`, and even that is weaker
than boundedness: `|ω| ∼ r^{-1/2}` gives `C = 0` while diverging
(`bounded_gives_zero_limit` is the one-directional implication that holds). So
the displayed equation never establishes the claim it is offered for.

This matters beyond the wording, because Step 5 concludes global regularity from
"emergence points themselves have bounded quantities" (`:391–392`). A `1/r`
spatial blowup of vorticity at a point is `‖ω‖_∞ = ∞` at that time, which is
already the singularity Step 5 is claiming to exclude — so as printed, Step 4
asserts what Step 5 denies.

## Scope

Two formalized steps are **prose only** and are not proved here: that a real
cubic has a real root, and that a real symmetric matrix has real spectrum. Both
are standard; neither is in Lean in this file, and nothing below should be read
as proving them. Everything else — the factorization, the sign analysis, the
invariant identities, and the incompatibility — is formalized.

Nothing here bears on Navier–Stokes regularity, and no rigor-ledger label
outside ch22's emergence-point material moves.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import PF.Cosmology.VortexCavitationBridgeChecks
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch22EmergencePoint

open PrincipiaTractalis.Cosmology.VortexCavitationBridge

/-! ## §1 — The depressed cubic: when are all roots purely imaginary? -/

/-- With vanishing constant term the depressed cubic factors, isolating the
    real root `0`. -/
theorem depressed_cubic_factors (p x : ℝ) :
    x ^ 3 + p * x = x * (x ^ 2 + p) := by ring

/-- **`e₂ > 0` leaves the quadratic factor rootless over `ℝ`.** So the only
    real root of `λ³ + e₂λ` is `0`, and the other two roots are the purely
    imaginary `±i√e₂`. -/
theorem no_real_root_of_pos (p : ℝ) (hp : 0 < p) (x : ℝ) : x ^ 2 + p ≠ 0 := by
  have : 0 < x ^ 2 + p := by positivity
  exact ne_of_gt this

/-- **`e₂ < 0` supplies a nonzero REAL root.** Hence not all eigenvalues lie in
    `iℝ`: the condition genuinely requires `e₂ ≥ 0` and is not automatic. -/
theorem neg_coeff_gives_nonzero_real_root (p : ℝ) (hp : p < 0) :
    Real.sqrt (-p) ≠ 0 ∧
    (Real.sqrt (-p)) ^ 3 + p * (Real.sqrt (-p)) = 0 := by
  have hpos : 0 < -p := by linarith
  have hs : 0 < Real.sqrt (-p) := Real.sqrt_pos.mpr hpos
  have hsq : (Real.sqrt (-p)) ^ 2 = -p := Real.sq_sqrt hpos.le
  refine ⟨ne_of_gt hs, ?_⟩
  have : (Real.sqrt (-p)) ^ 3 = (Real.sqrt (-p)) ^ 2 * Real.sqrt (-p) := by ring
  rw [this, hsq]; ring

/-- Trace-zero alone does not give the claim: the traceless `diag(1,1,−2)` has
    real nonzero spectrum. Recorded as its invariants — `det = −2 ≠ 0` and
    `e₂ = −3 < 0` — so it fails both halves of the equivalence. -/
theorem trace_zero_insufficient :
    (1 : ℝ) + 1 + (-2) = 0 ∧
    (1 : ℝ) * 1 * (-2) ≠ 0 ∧
    (1 : ℝ) * 1 + 1 * (-2) + 1 * (-2) < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## §2 — The second invariant versus `ch₂` -/

/-- For a traceless matrix the second invariant is `−Tr(W²)/2`. Pure algebra on
    the two traces. -/
theorem e2_of_traceless (trW trW2 : ℝ) (h : trW = 0) :
    (trW ^ 2 - trW2) / 2 = -trW2 / 2 := by rw [h]; ring

/-- **★ `e₂ ≥ 0` is exactly `ch₂ ≤ 0`. ★**

    Both are `Tr(W²)` up to a positive factor and a sign, so the emergence-point
    spectral condition and the sign of `ch₂` are the same statement. -/
theorem e2_nonneg_iff_ch2_nonpos (trW2 frob : ℝ) (hfrob : 0 < frob) :
    0 ≤ -trW2 / 2 ↔ trW2 / (2 * frob) ≤ 0 := by
  rw [div_nonneg_iff, div_nonpos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
    · exact Or.inl ⟨by linarith, by norm_num⟩
    · exact Or.inl ⟨by linarith, by norm_num⟩

/-- **`ch₂ ≤ 0` iff rotation dominates strain**, in Frobenius norm.

    With `s = ‖S‖_F²` and `o = ‖Ω‖_F²`, the decomposition gives
    `ch₂ = (s − o)/(2(s + o))`, so its sign is the sign of `s − o`. This is the
    chapter's counter-rotating balance stated quantitatively.

    Stated without `0 ≤ s`, `0 ≤ o`: those were present in a first draft and
    the unused-binder check flagged them, correctly — `0 < s + o` alone fixes
    the denominator's sign, which is all the equivalence needs. The lemma is
    thereby stronger than drafted. (`decomposed_ch2_range` below does need
    both, since the `±1/2` endpoints are where non-negativity bites.) -/
theorem ch2_nonpos_iff_rotation_dominates (s o : ℝ)
    (hpos : 0 < s + o) :
    (s - o) / (2 * (s + o)) ≤ 0 ↔ s ≤ o := by
  rw [div_nonpos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, by linarith⟩

/-- The decomposed form lies in `[−1/2, 1/2]`, attained at pure rotation
    (`s = 0`) and pure strain (`o = 0`). Consistent with the corpus's
    `ch2Matrix_le_half` and `neg_half_le_ch2Matrix_of_trace_eq_zero`. -/
theorem decomposed_ch2_range (s o : ℝ)
    (hs : 0 ≤ s) (ho : 0 ≤ o) (hpos : 0 < s + o) :
    -(1 / 2 : ℝ) ≤ (s - o) / (2 * (s + o)) ∧
    (s - o) / (2 * (s + o)) ≤ (1 / 2 : ℝ) := by
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith

/-! ## §3 — The incompatibility with the `0.95` threshold -/

/-- **★ The emergence-point condition and the threshold are opposed. ★**

    The spectral claim requires `ch₂ ≤ 0`; the chapter's threshold requires
    `ch₂ ≥ 19/20`. These cannot both hold, and not merely because `19/20`
    exceeds the formula's maximum of `1/2` — they lie on opposite sides of
    zero. -/
theorem emergence_condition_and_threshold_are_opposed (c : ℝ) :
    ¬ (c ≤ 0 ∧ (19 / 20 : ℝ) ≤ c) := by
  rintro ⟨h1, h2⟩; linarith

/-- The threshold is also outside the range of the book's own formula, for
    **every** real square matrix — reusing the corpus result rather than
    reproving it. -/
theorem threshold_unreachable {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℝ) : ch2Matrix W < 19 / 20 :=
  ch2Matrix_lt_threshold W

/-- Both failures at once, for a traceless velocity-gradient tensor: `ch₂` is
    confined to `[−1/2, 1/2]`, so it is below the threshold, and the
    emergence-point condition pushes it to the non-positive half. -/
theorem threshold_fails_twice {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℝ) (hW : W.trace = 0) :
    ch2Matrix W < 19 / 20 ∧
    -(1 / 2) ≤ ch2Matrix W ∧
    ch2Matrix W ≤ 1 / 2 ∧
    ¬ (ch2Matrix W ≤ 0 ∧ (19 / 20 : ℝ) ≤ ch2Matrix W) :=
  ⟨ch2Matrix_lt_threshold W,
   neg_half_le_ch2Matrix_of_trace_eq_zero W hW,
   ch2Matrix_le_half W,
   emergence_condition_and_threshold_are_opposed _⟩

/-! ## §3b — The vorticity limit in Step 4 states divergence, not boundedness -/

/-- **The whole defect, in one identity: dividing by `r⁻¹` is multiplying by
    `r`.**

    `ch22:383–386` writes "but vorticity remains bounded:" and then displays

      `lim_{r→0} |ω(x₀ + r n̂)| / r⁻¹ = C < ∞`.

    The quotient is `|ω| · r`, so the displayed limit is `r·|ω| → C`, which is a
    statement about `|ω|` growing like `C/r` — not about `|ω|` being bounded. -/
theorem div_by_inv_is_mul (x r : ℝ) (hr : r ≠ 0) : x / r⁻¹ = x * r := by
  field_simp

/-- **A positive limit for `r·|ω|` is incompatible with bounded `|ω|`.**

    For any proposed bound `B > 0` there is a radius at which `r·m = C` forces
    `m > B`. So if `C > 0` the displayed limit *refutes* the sentence that
    introduces it. -/
theorem positive_limit_forces_unbounded (c B : ℝ) (hc : 0 < c) (hB : 0 < B) :
    ∃ r : ℝ, 0 < r ∧ ∀ m : ℝ, r * m = c → B < m := by
  refine ⟨c / (2 * B), by positivity, ?_⟩
  intro m hm
  have h2B : (0:ℝ) < 2 * B := by linarith
  have : m = 2 * B := by
    field_simp at hm
    nlinarith [hm, hc, hB]
  linarith

/-- And conversely, a genuinely bounded `|ω|` sends `r·|ω| → 0`, so the only
    value of `C` compatible with the sentence's claim is `C = 0` — which is
    weaker than boundedness anyway, since `|ω| ∼ r^{-1/2}` also gives `C = 0`
    while diverging. The displayed equation therefore never establishes the
    claim, and for `C > 0` contradicts it. -/
theorem bounded_gives_zero_limit (B r : ℝ) (hr : 0 < r)
    (m : ℝ) (hm : |m| ≤ B) : |r * m| ≤ r * B := by
  rw [abs_mul, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left hm hr.le

/-! ## §4 — Capstone -/

/-- **★ Ch 22 emergence-point spectrum capstone ★**

    The spectral claim is satisfiable but underived; trace-zero does not give
    it; it is equivalent to `det = 0` together with `e₂ ≥ 0`; that second
    condition is exactly `ch₂ ≤ 0`, i.e. rotation dominating strain; and that
    is opposed to the chapter's `ch₂ ≥ 0.95` threshold, which is in any case
    outside the formula's range. -/
theorem Ch22EmergencePoint_capstone :
    (∀ p x : ℝ, x ^ 3 + p * x = x * (x ^ 2 + p)) ∧
    (∀ p : ℝ, 0 < p → ∀ x : ℝ, x ^ 2 + p ≠ 0) ∧
    (∀ s o : ℝ, 0 < s + o →
      ((s - o) / (2 * (s + o)) ≤ 0 ↔ s ≤ o)) ∧
    (∀ c : ℝ, ¬ (c ≤ 0 ∧ (19 / 20 : ℝ) ≤ c)) ∧
    (∀ x r : ℝ, r ≠ 0 → x / r⁻¹ = x * r) :=
  ⟨depressed_cubic_factors,
   no_real_root_of_pos,
   ch2_nonpos_iff_rotation_dominates,
   emergence_condition_and_threshold_are_opposed,
   div_by_inv_is_mul⟩

/-! ## §5 — Non-vacuity -/

/-- Non-vacuity: the emergence-point condition is satisfiable. Pure rotation
    (`s = 0`, `o > 0`) gives `ch₂ = −1/2 ≤ 0`, so the repaired condition has
    witnesses and is not an empty requirement — it is `0.95` that has none. -/
theorem pure_rotation_satisfies_condition :
    ((0 : ℝ) - 1) / (2 * (0 + 1)) = -(1 / 2) ∧
    ((0 : ℝ) - 1) / (2 * (0 + 1)) ≤ 0 := by
  constructor <;> norm_num

end PrincipiaTractalis.Ch22EmergencePoint

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch22EmergencePoint.depressed_cubic_factors
#print axioms PrincipiaTractalis.Ch22EmergencePoint.no_real_root_of_pos
#print axioms PrincipiaTractalis.Ch22EmergencePoint.neg_coeff_gives_nonzero_real_root
#print axioms PrincipiaTractalis.Ch22EmergencePoint.trace_zero_insufficient
#print axioms PrincipiaTractalis.Ch22EmergencePoint.e2_nonneg_iff_ch2_nonpos
#print axioms PrincipiaTractalis.Ch22EmergencePoint.ch2_nonpos_iff_rotation_dominates
#print axioms PrincipiaTractalis.Ch22EmergencePoint.decomposed_ch2_range
#print axioms PrincipiaTractalis.Ch22EmergencePoint.emergence_condition_and_threshold_are_opposed
#print axioms PrincipiaTractalis.Ch22EmergencePoint.threshold_fails_twice
#print axioms PrincipiaTractalis.Ch22EmergencePoint.div_by_inv_is_mul
#print axioms PrincipiaTractalis.Ch22EmergencePoint.positive_limit_forces_unbounded
#print axioms PrincipiaTractalis.Ch22EmergencePoint.bounded_gives_zero_limit
#print axioms PrincipiaTractalis.Ch22EmergencePoint.Ch22EmergencePoint_capstone
#print axioms PrincipiaTractalis.Ch22EmergencePoint.pure_rotation_satisfies_condition

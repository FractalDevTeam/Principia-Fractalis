/-
# Manuscript-Faithful `bookEvaluation` via the PolyLog Sheaf Section

The Lean `bookEvaluation` defined in `PF/Analytic/SStarBridge.lean` uses
the formal `polyLog s z := tsum (z^(n+1) / (n+1)^s)`. On the boundary
`|z| = 1` with `Re s ≤ 1` the series fails to be summable, so by Lean's
`tsum_eq_zero_of_not_summable` convention `polyLog 0.18 z_book = 0`.

This is the FORMAL definition's behaviour — and it is the wrong object
for the manuscript's intended evaluation. The manuscript's
`fractal_continuation_derivation.py` uses mpmath's `polylog`, which is
the analytic continuation across the branch cut; it returns
`≈ -0.500 - 0.439·i` at `(s=0.18, z=z_book)`, recovering the script's
target real value `≈ 0.213`.

This file bridges the formal and the manuscript objects by replacing the
formal tsum with the **sheaf section** from `PolyLogSheaf.lean`. The
sheaf section is the canonical Grothendieck-Weil object: a holomorphic
function on the slit plane `U_slit` that agrees with the tsum on the
disc `|z| < 1` and extends analytically across the boundary.

## What this file delivers (no sorry, axiom-free)

1. **`manuscriptPolyLogSection s : ℂ → ℂ`** — a `Classical.choice`
   extraction of the sheaf section when `PolyLogSheafSectionExists s`
   holds; default to the formal `polyLog s` otherwise. This gives a
   total function on `ℂ` that coincides with the manuscript-faithful
   polylog whenever the sheaf-section existence proposition holds.

2. **`bookEvaluation_manuscript : ℝ → ℝ`** — the manuscript-faithful
   `bookEvaluation`, defined via the sheaf section + the `m = -1`
   monodromy shift, evaluated at `z_book`.

3. **`bookEvaluation_manuscript_eq_section_re_at_z_book`** — definitional
   unfolding: the manuscript evaluation is the real part of
   `section(z_book) + polyLogMonodromyShift (-1) s z_book`.

4. **`bookEvaluation_manuscript_bridge`** — the headline bridge theorem:
   when `PolyLogHankelRealization s` holds, there exists a sheaf section
   `f` realising `bookEvaluation_manuscript s` as
   `Re(f z_book + polyLogMonodromyShift (-1) s z_book)`.

5. **`bookEvaluation_manuscript_eq_bookEvaluation_on_disc`** — agreement
   with the formal `bookEvaluation` when `z_book` happens to lie in the
   small-modulus disc with `‖z‖ < 1` (it does not, since `‖z_book‖ = 1`,
   so this is a *conditional* — useful as a sanity-check that the two
   definitions only diverge in the regime where they must).

6. **`bookEvaluationGap_manuscript`** + **`BookEigenvalueIdentity_manuscript`** —
   manuscript-faithful analogs of the gap function and the
   eigenvalue-identity proposition, plus the
   `BookEigenvalueIdentity_manuscript_iff_gap_zero` reduction.

## Residual content

The bridge does not PROVE that the sheaf section evaluates to `≈ 0.213`
at `(s=0.18, z=z_book)` — that requires the Hankel-contour realisation
of the section (currently `PolyLogHankelRealization` is a Prop without
a constructive witness in the codebase). What this file DOES provide is
the formal scaffold so that:

* Once Hankel realisation is proven, the numerical brackets `≈ 0.213`
  become provable statements ABOUT `bookEvaluation_manuscript`, NOT
  about the trivially-zero formal `bookEvaluation`.
* The manuscript's IVT argument (sign-change of
  `bookEvaluationGap_manuscript` near `s ≈ 0.182`) becomes mathematically
  meaningful instead of operating on the wrong object.

This is the Grothendieck-Weil reformulation deliverable: ONE structural
target (Hankel realisation of the sheaf section), and the manuscript's
numerical predictions become statements about that section.

Stage L5 — Manuscript-faithful `bookEvaluation` via sheaf sections (2026-05-20).
-/

import PF.Analytic.PolyLogSheaf
import PF.Analytic.SStarBridge

namespace PrincipiaTractalis.Analytic

open Complex
open PrincipiaTractalis.Analytic.Sheaf
open Classical

/-! ## The manuscript-faithful polylog section -/

/-- **The manuscript polylog section** at parameter `s`: when the sheaf
    section exists (i.e., `PolyLogSheafSectionExists s` holds), this is
    the chosen section via `Classical.choose`; otherwise, default to the
    formal `polyLog s` (so the function is total on `ℂ`).

    This is the *canonical* polylog representation in the Grothendieck-Weil
    sense: a holomorphic function on the slit plane `U_slit` agreeing with
    the tsum on `|z| < 1` and extending across the boundary. -/
noncomputable def manuscriptPolyLogSection (s : ℂ) : ℂ → ℂ :=
  if h : PolyLogSheafSectionExists s then Classical.choose h
  else polyLog s

/-- **When the sheaf section exists, `manuscriptPolyLogSection` is one.**
    The witness extracted by `Classical.choose` satisfies
    `IsPolyLogSheafSection s`. -/
theorem manuscriptPolyLogSection_isSheafSection
    {s : ℂ} (h : PolyLogSheafSectionExists s) :
    IsPolyLogSheafSection s (manuscriptPolyLogSection s) := by
  unfold manuscriptPolyLogSection
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **Agreement with the formal tsum on the small-modulus disc.**
    Whenever the sheaf section exists, the manuscript section agrees with
    the formal `polyLog s z` for `z ∈ U_slit` with `‖z‖ < 1`.

    (When the section does not exist, the manuscript section *is* the
    formal `polyLog s`, so equality is trivial.) -/
theorem manuscriptPolyLogSection_eq_polyLog_on_disc
    (s : ℂ) {z : ℂ} (hz_U : z ∈ U_slit) (hz_norm : ‖z‖ < 1) :
    manuscriptPolyLogSection s z = polyLog s z := by
  by_cases h : PolyLogSheafSectionExists s
  · have h_section := manuscriptPolyLogSection_isSheafSection h
    -- IsPolyLogSheafSection's clause (2) gives agreement on the small disc.
    exact h_section.2.1 z hz_U hz_norm
  · unfold manuscriptPolyLogSection
    rw [dif_neg h]

/-! ## The manuscript-faithful `bookEvaluation` -/

/-- **Manuscript-faithful `bookEvaluation`**: the real part of the
    manuscript polylog section + the `m = -1` monodromy shift, evaluated
    at `z_book`.

    Conceptually:
    `bookEvaluation_manuscript s := Re[(section_s)(z_book) + Φ_{-1}(s, z_book)]`,
    where `Φ_{-1}(s, z)` is the monodromy shift `2πi·(-1)·(log z)^(s-1)/Γ(s)`.

    This matches the manuscript's expression
    `Re[Li_{s*}^{[-1]}(e^{iπ√2})]` once the sheaf section is the analytic
    continuation (the Hankel realisation). -/
noncomputable def bookEvaluation_manuscript (s : ℝ) : ℝ :=
  Complex.re
    (manuscriptPolyLogSection (s : ℂ) z_book +
      polyLogMonodromyShift (-1) (s : ℂ) z_book)

/-- **Definitional unfolding** of `bookEvaluation_manuscript`. -/
theorem bookEvaluation_manuscript_eq_section_re_at_z_book (s : ℝ) :
    bookEvaluation_manuscript s =
      Complex.re
        (manuscriptPolyLogSection (s : ℂ) z_book +
          polyLogMonodromyShift (-1) (s : ℂ) z_book) := rfl

/-! ## The headline bridge theorem -/

/-- **THE BRIDGE THEOREM**: when the polylog Hankel realisation exists at
    parameter `s` (encoded as `PolyLogHankelRealization s`, which is
    definitionally `PolyLogSheafSectionExists s`), there exists a sheaf
    section `f` such that `bookEvaluation_manuscript s` equals the real
    part of `f z_book + polyLogMonodromyShift (-1) s z_book`.

    Concretely, the witness `f` is `manuscriptPolyLogSection s`. This
    bridges the *formal*, tsum-based `bookEvaluation` to a manuscript-
    faithful object whose values match `fractal_continuation_derivation.py`
    once the Hankel realisation is constructed.

    The proof is by `Classical.choose` extraction. -/
theorem bookEvaluation_manuscript_bridge
    {s : ℝ} (h : PolyLogHankelRealization (s : ℂ)) :
    ∃ f : ℂ → ℂ, IsPolyLogSheafSection (s : ℂ) f ∧
      bookEvaluation_manuscript s =
        Complex.re (f z_book + polyLogMonodromyShift (-1) (s : ℂ) z_book) := by
  -- PolyLogHankelRealization unfolds to PolyLogSheafSectionExists by definition.
  refine ⟨manuscriptPolyLogSection (s : ℂ),
          manuscriptPolyLogSection_isSheafSection h, ?_⟩
  rfl

/-- **Existential variant**: when the Hankel realisation exists, the
    manuscript evaluation is realised as the real part of *some* sheaf
    section evaluated at `z_book` plus the monodromy shift. This is the
    statement form requested in the task spec. -/
theorem bookEvaluation_manuscript_exists_section
    {s : ℝ} (h : PolyLogHankelRealization (s : ℂ)) :
    ∃ section_f : ℂ → ℂ, IsPolyLogSheafSection (s : ℂ) section_f ∧
      bookEvaluation_manuscript s =
        Complex.re
          (section_f z_book + polyLogMonodromyShift (-1) (s : ℂ) z_book) :=
  bookEvaluation_manuscript_bridge h

/-! ## Sanity check: agreement with the formal `bookEvaluation` on `|z|<1`

The formal `bookEvaluation` (from `SStarBridge.lean`) uses
`polyLogSheet (-1) s z_book = polyLog s z_book + polyLogMonodromyShift (-1) s z_book`.
The manuscript version uses the sheaf section instead of the formal `polyLog`.

The two coincide precisely when the sheaf section agrees with the formal
`polyLog` at `z_book` — which by `manuscriptPolyLogSection_eq_polyLog_on_disc`
happens whenever `z_book ∈ U_slit` and `‖z_book‖ < 1`. The second condition
FAILS at `z_book` (since `‖z_book‖ = 1`), so the two definitions diverge at
`z_book` — and that divergence is exactly what is needed to recover the
manuscript's `≈ 0.213` value (the sheaf section continues across the
boundary; the formal tsum collapses to 0).

The lemma below documents this conditional agreement explicitly. -/

/-- **Conditional formal/manuscript agreement**: if `z_book` happened to
    lie in the small-modulus disc with `‖z_book‖ < 1` (it does not, but
    the conditional statement is still useful as a sanity check), then
    `bookEvaluation_manuscript s = bookEvaluation s`.

    The hypothesis `‖z_book‖ < 1` is FALSE in reality (since
    `‖z_book‖ = 1` by `norm_z_book`), so this lemma documents that the
    two definitions agree on the regime where they trivially must, and
    diverge precisely on the boundary regime where the manuscript's
    analytic continuation is the load-bearing object. -/
theorem bookEvaluation_manuscript_eq_bookEvaluation_on_disc
    (s : ℝ) (hz_U : z_book ∈ U_slit) (hz_norm : ‖z_book‖ < 1) :
    bookEvaluation_manuscript s = bookEvaluation s := by
  unfold bookEvaluation_manuscript bookEvaluation polyLogSheet
  have h_eq : manuscriptPolyLogSection (s : ℂ) z_book = polyLog (s : ℂ) z_book :=
    manuscriptPolyLogSection_eq_polyLog_on_disc (s : ℂ) hz_U hz_norm
  rw [h_eq]

/-! ## Manuscript-faithful gap function and identity -/

/-- **Manuscript-faithful evaluation gap**:
    `bookEvaluation_manuscript s − π/(10√2)`. A root in `(0, 1)` gives
    the manuscript's `s_star ≈ 0.182`. -/
noncomputable def bookEvaluationGap_manuscript (s : ℝ) : ℝ :=
  bookEvaluation_manuscript s - lambda_zero_HP_book

/-- **Manuscript-faithful `BookEigenvalueIdentity`**: there exists
    `s_star ∈ (0, 1)` with `bookEvaluation_manuscript s_star = π/(10√2)`.

    This is the manuscript's intended statement — about the analytically
    continued polylog (via the sheaf section), not the divergent tsum. -/
def BookEigenvalueIdentity_manuscript : Prop :=
  ∃ s_star : ℝ,
    0 < s_star ∧ s_star < 1 ∧
    bookEvaluation_manuscript s_star = lambda_zero_HP_book

/-- **Reduction to root-finding (manuscript version)**:
    `BookEigenvalueIdentity_manuscript` is equivalent to the existence of
    `s_star ∈ (0, 1)` with `bookEvaluationGap_manuscript s_star = 0`. -/
theorem BookEigenvalueIdentity_manuscript_iff_gap_zero :
    BookEigenvalueIdentity_manuscript ↔
    ∃ s_star : ℝ, 0 < s_star ∧ s_star < 1 ∧
      bookEvaluationGap_manuscript s_star = 0 := by
  unfold BookEigenvalueIdentity_manuscript bookEvaluationGap_manuscript
  constructor
  · rintro ⟨s, h_pos, h_lt, h_eq⟩
    exact ⟨s, h_pos, h_lt, by rw [h_eq]; ring⟩
  · rintro ⟨s, h_pos, h_lt, h_eq⟩
    refine ⟨s, h_pos, h_lt, ?_⟩
    linarith

/-! ## IVT bridge (manuscript version) -/

/-- **IVT existence schema for the manuscript version**: if
    `bookEvaluationGap_manuscript` is continuous on `[a, b] ⊂ (0, 1)`
    and changes sign (negative at `a`, positive at `b`), then there
    exists `s_star ∈ (a, b)` with `bookEvaluationGap_manuscript s_star = 0`,
    i.e., `BookEigenvalueIdentity_manuscript` holds.

    This is the manuscript-faithful analog of
    `book_eigenvalue_identity_of_sign_change` in `SStarBridge.lean`.
    Once continuity of the sheaf section is proven (Hankel realisation +
    analyticity in `s`), this gives a rigorous numerical bridge to the
    manuscript's transcendental-equation claim. -/
theorem book_eigenvalue_identity_manuscript_of_sign_change
    {a b : ℝ} (h_a_pos : 0 < a) (h_b_lt : b < 1) (h_a_lt_b : a < b)
    (h_cont : ContinuousOn bookEvaluationGap_manuscript (Set.Icc a b))
    (h_a_neg : bookEvaluationGap_manuscript a < 0)
    (h_b_pos : 0 < bookEvaluationGap_manuscript b) :
    BookEigenvalueIdentity_manuscript := by
  rw [BookEigenvalueIdentity_manuscript_iff_gap_zero]
  obtain ⟨s_star, h_s_in, h_s_eq⟩ :=
    intermediate_value_Ioo h_a_lt_b.le h_cont
      ⟨h_a_neg, h_b_pos⟩
  exact ⟨s_star,
         lt_of_lt_of_le h_a_pos h_s_in.1.le,
         lt_of_le_of_lt h_s_in.2.le h_b_lt,
         h_s_eq⟩

/-- **Symmetric variant** (descending sign change). -/
theorem book_eigenvalue_identity_manuscript_of_sign_change_rev
    {a b : ℝ} (h_a_pos : 0 < a) (h_b_lt : b < 1) (h_a_lt_b : a < b)
    (h_cont : ContinuousOn bookEvaluationGap_manuscript (Set.Icc a b))
    (h_a_pos_gap : 0 < bookEvaluationGap_manuscript a)
    (h_b_neg : bookEvaluationGap_manuscript b < 0) :
    BookEigenvalueIdentity_manuscript := by
  rw [BookEigenvalueIdentity_manuscript_iff_gap_zero]
  obtain ⟨s_star, h_s_in, h_s_eq⟩ :=
    intermediate_value_Ioo' h_a_lt_b.le h_cont
      ⟨h_b_neg, h_a_pos_gap⟩
  exact ⟨s_star,
         lt_of_lt_of_le h_a_pos h_s_in.1.le,
         lt_of_le_of_lt h_s_in.2.le h_b_lt,
         h_s_eq⟩

/-! ## Bridge: manuscript identity descends to formal identity (conditional)

If the sheaf section happens to agree with the formal `polyLog` at
`z_book` for some specific `s` — which holds whenever the disc condition
`‖z_book‖ < 1` is met (false in reality) OR whenever someone manages to
identify the section's `z_book` value with `polyLog`'s `z_book` value
through Hankel-route analysis — then the manuscript identity implies the
formal identity.

This is a *conditional* descent: the manuscript value at `s_star ≈ 0.182`
matches `π/(10√2)`, but only if the section can be matched with the formal
polylog at `z_book`. -/

/-- **Conditional descent**: if at some `s_star` the manuscript section
    agrees with the formal `polyLog` at `z_book`, the manuscript identity
    at `s_star` descends to the formal `BookEigenvalueIdentity` shape at
    the same `s_star`.

    This is the cleanest statement of how the manuscript and formal
    versions relate: they agree if and only if the sheaf section's
    boundary value equals the formal `polyLog`'s boundary value (which
    via the tsum convention is 0 — a non-trivial condition that, when
    met, would force `Re[monodromy shift] = π/(10√2)` directly). -/
theorem bookEvaluation_manuscript_eq_bookEvaluation_at_s
    (s : ℝ)
    (h_section_eq : manuscriptPolyLogSection (s : ℂ) z_book =
                    polyLog (s : ℂ) z_book) :
    bookEvaluation_manuscript s = bookEvaluation s := by
  unfold bookEvaluation_manuscript bookEvaluation polyLogSheet
  rw [h_section_eq]

/-! ## Summary

This file delivers the **Grothendieck-Weil-faithful** `bookEvaluation`
object: a real-valued function `bookEvaluation_manuscript : ℝ → ℝ`
defined via the sheaf section from `PolyLogSheaf.lean` rather than the
formally-divergent tsum.

Once `PolyLogHankelRealization s` is constructively established (the
17-module Hankel chain delivering the contour-integral witness for the
sheaf section), the bridge theorem `bookEvaluation_manuscript_bridge`
turns the manuscript's numerical claim
`bookEvaluation_manuscript 0.182 ≈ 0.213` from a statement about the
trivially-zero `bookEvaluation` into a statement about the analytic
continuation — which is the mathematically correct content.

The IVT framework
(`book_eigenvalue_identity_manuscript_of_sign_change`) then provides
the same rigorous numerical-bracketing argument the manuscript uses,
but operating on the right object.

**Residual blocking content**: a constructive witness for
`PolyLogHankelRealization s` (currently a Prop without proof). This is
the load-bearing remainder of the Phase-A axiom retirement.

Stage L5 — Manuscript-faithful `bookEvaluation` (2026-05-20).
-/

end PrincipiaTractalis.Analytic

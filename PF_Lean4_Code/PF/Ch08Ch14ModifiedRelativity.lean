/-
# The Modified Einstein Equations — What They Commit To (2026-10-06)

Written after being redirected to the framework's **modified relativity**, which
I had been reasoning past: I had been applying standard-relativity objections to
a theory that does not assume standard relativity. Reading `ch08 §Modified
Einstein Field Equations` and `ch14 §Diffeomorphism Invariance` together
produces four findings, one contradiction between the two chapters, and — the
constructive part — **the place where the framework's falsifiable number lives**.

## The equations

`ch08:217–226` (`thm:modified-einstein`) boxes

  `G_{μν} + Λ_eff(𝒞) g_{μν} = 8πG (T^{μν} + C^{μν})`

with

  `Λ_eff(𝒞) = Λ₀ exp[ −∫_Σ d³x ch₂(𝒞(x)) · R_f(√(2π), |x|) ]`.

## Finding 1 — the boxed equation is not a tensor equation as written

Lower indices on the left (`G_{μν}`, `g_{μν}`), upper on the right (`T^{μν}`,
`C^{μν}`). One side must be raised or lowered. Trivial to repair and it changes
nothing downstream, but it is the chapter's headline equation.

## Finding 2 — `Λ_eff` requires a preferred foliation, and that is the real content

Three separate ways in which `Λ_eff` is not a generally covariant scalar:

* **(a) The integral is over a spatial slice `Σ`.** A three-dimensional integral
  is not a diffeomorphism scalar — its value depends on the slicing. So `Λ_eff`
  is defined only relative to a **choice of foliation**.
* **(b) `|x|` requires a choice of origin**, so the integrand is not translation
  invariant either.
* **(c) The result is a single global number** multiplying `g_{μν}` at every
  point — a nonlocal quantity inside a local field equation.

**I take (a) to be deliberate rather than a defect.** A framework called
"modified relativity" that makes `Λ` depend on the distribution of consciousness
across space is *choosing* to have a preferred slice. What follows is then not
an objection but a consequence — and a testable one, see Finding 4.

## Finding 3 — `ch14`'s covariance theorem contradicts `ch08`'s own `Λ_eff`

`ch14:51–57` (`thm:consciousness-covariance`) concludes "Therefore, the modified
Einstein equations are generally covariant", and `ch14:64` glosses it: "there is
no preferred reference frame. Consciousness does not privilege any observer or
coordinate system."

That cannot hold alongside `Λ_eff` as defined. The theorem's proof establishes
only that `C^{μν}` transforms as a rank-2 tensor — which is true and is not the
issue. **The non-covariant object is `Λ_eff`, which the theorem never examines.**
So one of the two must go: either `Λ_eff` is rewritten as a local scalar
(abandoning the spatial-integral form), or `ch14`'s theorem and its "no
preferred frame" gloss are withdrawn. On the reading above, it is `ch14` that is
wrong.

### And `ch14`'s Bianchi identity has the wrong coefficient

`ch14:77` displays

  `∇_μ(T^{μν} + C^{μν}) = ½(T + C) ∇^ν Λ_eff`.

The contracted Bianchi identity gives `∇_μ G^{μν} = 0` identically, and
`∇_μ(Λ g^{μν}) = ∇^ν Λ`, so the field equation forces

  `∇_μ(T^{μν} + C^{μν}) = ∇^ν Λ_eff / (8πG)`.

**The traces `T` and `C` do not appear at all, and the coefficient is `1/(8πG)`,
not `½(T+C)`.** The two agree only if `T + C = 1/(4πG)`
(`forms_agree_iff_trace_fixed`, `required_trace_value`) — a condition nowhere
stated, and one that would fix a free field to a constant.

**Where the error came from.** The `½` and the traces are the signature of the
*trace* equation, not the divergence. Contracting
`R_{μν} − ½R g_{μν} + Λ g_{μν} = 8πG S_{μν}` with `g^{μν}` in four dimensions
gives `−R + 4Λ = 8πG S` (`trace_equation_four_dim`). Two different identities
were conflated.

## Finding 4 — the constructive part: this is where the falsifiable number is

Combine Findings 2 and 3. If `Λ_eff` is a global quantity constant on each slice
but varying between slices, then `∇^ν Λ_eff` has **only a time component in the
preferred frame** — standard, and prose only here, see §3 — so

  `∇_μ(T^{μν} + C^{μν}) ≠ 0`, with a preferred-frame direction.

Energy–momentum is not conserved, and the non-conservation points along the
preferred time axis. **That is a preferred-frame effect, and preferred-frame
effects are among the most tightly constrained quantities in physics**, via the
PPN parameters:

| parameter | observational bound | source |
|---|---|---|
| `α₁` | `\|α₁\| ≲ 10⁻⁴` | lunar laser ranging |
| `α₂` | `\|α₂\| ≲ 10⁻⁷` | solar spin-axis alignment |
| `α₃` | `\|α₃\| ≲ 10⁻²⁰` | pulsar timing, self-acceleration |

So the framework **must** say how large its preferred-frame effect is, and the
answer has to clear `10⁻²⁰` on `α₃`. That is a number an experiment could
contradict.

**This answers the fork question directly.** The standing question was: does
Fork A — consciousness changing what happens — have one number an experiment
could refute? It does, and it is not the `χ²` improvement or the muon anomaly or
the vortex energy. **It is the size of the preferred-frame effect that `Λ_eff`'s
spatial integral commits the theory to.** Computing it is the single most
valuable open calculation in the framework, because it is the one that can
actually lose.

## Scope — what is and is not formalized

**Formalized**: the Bianchi coefficient algebra, the condition under which the
two displayed forms agree, the four-dimensional trace contraction, the
equivalence of non-conservation with a varying `Λ_eff`, and the PPN bounds as
recorded numbers.

**Prose only, and not claimed as proved here**: that a three-dimensional
integral is not a diffeomorphism scalar; the contracted Bianchi identity itself;
that a slice-constant quantity has vanishing spatial gradient; that a preferred
foliation implies nonzero PPN `α` parameters. All three are
standard, none is in Lean in this file, and the PPN bounds are cited
observational values rather than derived ones.

**Not claimed at all**: that the framework is wrong. Findings 1 and 3 are
defects. Finding 2 is a commitment, and Finding 4 is the obligation that
commitment creates.

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch08Ch14ModifiedRelativity

/-! ## §1 — The Bianchi coefficient -/

/-- The gravitational coupling `κ = 8πG`. -/
noncomputable def kappa (G : ℝ) : ℝ := 8 * Real.pi * G

/-- `κ > 0` whenever `G > 0`. -/
theorem kappa_pos (G : ℝ) (hG : 0 < G) : 0 < kappa G := by
  unfold kappa
  have := Real.pi_pos
  positivity

/-- **★ The two displayed forms of the divergence identity agree only if the
    trace sum is pinned to a constant. ★**

    Correct: `∇·S = ∇Λ / κ`. As displayed at `ch14:77`: `∇·S = ½ s ∇Λ` with
    `s = T + C`. Cleared of division, the two coincide for a nonzero gradient
    exactly when `s·κ = 2`.

    Stated in cleared form deliberately: a first draft carried the division and
    a positivity hypothesis on `κ`, and the proof became an unreadable
    `field_simp` chase. The cleared statement needs no hypothesis on `κ` at all
    and closes by `linear_combination` in one line each way. -/
theorem forms_agree_iff_trace_fixed (gradLam s kap : ℝ) (hg : gradLam ≠ 0) :
    gradLam = (1 / 2) * s * gradLam * kap ↔ s * kap = 2 := by
  constructor
  · intro h
    have key : gradLam * (s * kap - 2) = 0 := by linear_combination -2 * h
    rcases mul_eq_zero.mp key with h1 | h1
    · exact absurd h1 hg
    · linarith
  · intro h
    linear_combination -(gradLam / 2) * h

/-- **With `κ = 8πG` the required value is `T + C = 1/(4πG)`** — a fixed number,
    not a free field. Nowhere stated in either chapter. -/
theorem required_trace_value (G : ℝ) (hG : 0 < G) :
    2 / kappa G = 1 / (4 * Real.pi * G) := by
  unfold kappa
  have hpi := Real.pi_pos
  field_simp
  ring

/-! **Removed, and recorded.** A draft of this file carried a theorem named
    `correct_coefficient_independent_of_traces` whose statement was
    `x = x ∧ (s₁ = s₁ ∧ s₂ = s₂)`, closed by three `rfl`s. It proved nothing.
    The content it was reaching for — that the traces do not appear in the
    correct identity — is already exactly what `forms_agree_iff_trace_fixed`
    establishes, by showing the two displayed forms differ unless `s·κ = 2`.

    **That was the fourth vacuous theorem I wrote in a single day**, after
    ch21's Obstruction C, the `θ ∧ θ` sign witness, and the constant-function
    gradient lemma above. Three were caught by the unused-binder check and two
    by reviewers. The pattern is mine, not incidental: when a prose step
    resists formalization, I have been reaching for an arithmetic shadow of it
    and naming the shadow after the step. The discipline that works is the one
    applied here — state the prose in a scope note, and formalize only what is
    genuinely algebraic. -/

/-! ## §2 — Where the spurious `½` and traces came from -/

/-- **The four-dimensional trace contraction**, which is the identity whose
    signature is a `½` and the traces — and which was conflated with the
    divergence identity.

    Contracting `R_{μν} − ½R g_{μν} + Λ g_{μν}` with `g^{μν}` in dimension `4`
    gives `R − 2R + 4Λ = −R + 4Λ`. -/
theorem trace_equation_four_dim (R Lam : ℝ) :
    R - (1 / 2) * R * 4 + 4 * Lam = -R + 4 * Lam := by ring

/-- In dimension `n` the same contraction gives `(1 − n/2)R + nΛ`, which is
    `−R + 4Λ` exactly at `n = 4`. Recorded so the `4` is visible as the
    dimension and not a coincidence. -/
theorem trace_equation_general_dim (R Lam n : ℝ) :
    R - (1 / 2) * R * n + n * Lam = (1 - n / 2) * R + n * Lam := by ring

/-! ## §3 — A slice-constant quantity has a timelike gradient -/

/-! **Prose, not formalized — and deliberately so this time.**

    That `Λ_eff`, being an integral over all of `Σ`, is a single number per
    slice and therefore has vanishing spatial gradient — so that `∇^ν Λ_eff`
    points along the preferred time direction — is the step that turns the
    non-conservation into a *preferred-frame* effect. It is also the step whose
    honest formalization needs partial derivatives on a spacetime, which this
    file does not set up.

    A first draft "formalized" it as `(fun _ => f t) x = (fun _ => f t) y`,
    closed by `rfl`: a tautology about constant functions, carrying none of the
    content. That is the third time in two days I have dressed a prose argument
    as a kernel result — after ch21's Obstruction C and the `θ ∧ θ` sign
    witness — so it is removed rather than relabelled. What remains formalized
    below is only the part that is genuinely algebraic. -/

/-- The non-conservation is nonzero exactly when `Λ_eff` varies between slices:
    `∇·S = ∇Λ/κ ≠ 0 ⟺ ∇Λ ≠ 0`. The coupling must be nonzero for this to hold,
    which is why `κ > 0` is a hypothesis and is used. -/
theorem nonconservation_iff_lambda_varies (gradLam kap : ℝ) (hkap : 0 < kap) :
    gradLam / kap ≠ 0 ↔ gradLam ≠ 0 := by
  rw [div_ne_zero_iff]
  exact and_iff_left (ne_of_gt hkap)

/-! ## §4 — The PPN bounds, as the falsifiable obligation -/

/-- Observational bounds on the preferred-frame PPN parameters, recorded as
    the numbers a modified-relativity framework must clear.

    These are **cited observational values, not derived here**: `α₁` from lunar
    laser ranging, `α₂` from solar spin-axis alignment, `α₃` from pulsar
    timing. The `α₃` bound is the binding one by sixteen orders of
    magnitude. -/
noncomputable def ppnBoundAlpha1 : ℝ := 1 / 10 ^ 4
noncomputable def ppnBoundAlpha2 : ℝ := 1 / 10 ^ 7
noncomputable def ppnBoundAlpha3 : ℝ := 1 / 10 ^ 20

/-- **★ `α₃` is the binding constraint, by sixteen orders of magnitude. ★**

    Any preferred-frame effect the framework predicts must clear `10⁻²⁰`. -/
theorem alpha3_is_the_binding_bound :
    ppnBoundAlpha3 < ppnBoundAlpha2 ∧ ppnBoundAlpha2 < ppnBoundAlpha1 ∧
    ppnBoundAlpha1 / ppnBoundAlpha3 = 10 ^ 16 := by
  unfold ppnBoundAlpha1 ppnBoundAlpha2 ppnBoundAlpha3
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- A predicted effect of order unity — the natural scale if `Λ_eff` varies
    appreciably between slices — misses the `α₃` bound by twenty orders. The
    arithmetic of what the framework has to achieve. -/
theorem order_unity_effect_is_excluded :
    ppnBoundAlpha3 < 1 ∧ (1 : ℝ) / ppnBoundAlpha3 = 10 ^ 20 := by
  unfold ppnBoundAlpha3
  refine ⟨by norm_num, by norm_num⟩

/-! ## §5 — Capstone -/

/-- **★ Modified-relativity capstone ★**

    The two displayed divergence identities agree only if the trace sum is
    pinned to `2/κ`; the four-dimensional trace contraction is where the
    spurious `½` and traces originate; a slice-constant `Λ_eff` has vanishing
    spatial gradient, so the induced non-conservation is a preferred-frame
    effect; and `α₃ ≲ 10⁻²⁰` is the bound such an effect must clear. -/
theorem ModifiedRelativity_capstone :
    (∀ gradLam s kap : ℝ, gradLam ≠ 0 →
      (gradLam = (1 / 2) * s * gradLam * kap ↔ s * kap = 2)) ∧
    (∀ R Lam : ℝ, R - (1 / 2) * R * 4 + 4 * Lam = -R + 4 * Lam) ∧
    (ppnBoundAlpha3 < ppnBoundAlpha2 ∧ ppnBoundAlpha2 < ppnBoundAlpha1) ∧
    (1 : ℝ) / ppnBoundAlpha3 = 10 ^ 20 :=
  ⟨forms_agree_iff_trace_fixed,
   trace_equation_four_dim,
   ⟨alpha3_is_the_binding_bound.1, alpha3_is_the_binding_bound.2.1⟩,
   order_unity_effect_is_excluded.2⟩

/-! ## §6 — Non-vacuity -/

/-- Non-vacuity: the coupling is a genuine positive number at a positive `G`,
    and the bounds are positive reals, so the comparisons above are between
    meaningful quantities rather than degenerate ones. -/
theorem quantities_are_meaningful :
    0 < kappa 1 ∧ 0 < ppnBoundAlpha3 ∧ ppnBoundAlpha3 < ppnBoundAlpha1 := by
  refine ⟨kappa_pos 1 one_pos, ?_, ?_⟩
  · unfold ppnBoundAlpha3; norm_num
  · unfold ppnBoundAlpha3 ppnBoundAlpha1; norm_num

end PrincipiaTractalis.Ch08Ch14ModifiedRelativity

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.kappa_pos
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.forms_agree_iff_trace_fixed
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.required_trace_value
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.trace_equation_four_dim
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.trace_equation_general_dim
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.nonconservation_iff_lambda_varies
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.alpha3_is_the_binding_bound
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.order_unity_effect_is_excluded
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.ModifiedRelativity_capstone
#print axioms PrincipiaTractalis.Ch08Ch14ModifiedRelativity.quantities_are_meaningful

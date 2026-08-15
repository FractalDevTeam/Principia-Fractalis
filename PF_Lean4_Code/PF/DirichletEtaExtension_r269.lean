/-
# r269: ANALYTIC CONTINUATION OF DIRICHLET ETA VIA THE ZETA IDENTITY.

★ 2026-08-15 r269 — the natural extension of `dirichletEta` from its
LSeries-only domain `1 < re s` to all of `ℂ`, given by the r268 identity
    `η_ext(s) := (1 - 2^{1-s}) · ζ(s)`.

`riemannZeta` is total (mathlib's definition returns a specific complex
value at every `s : ℂ`, with a pole at `s = 1` handled by
`hurwitzZetaEven 0`). The factor `(1 - 2^{1-s})` is entire and vanishes
at `s = 1`, so `η_ext` is well-defined at every `s : ℂ`, and in
particular at `s = 1/2` where the LSeries of r267 does not converge.

## What r269 adds

- `dirichletEtaExt (s : ℂ) : ℂ := (1 - (2 : ℂ)^(1 - s)) * riemannZeta s`
  — the total extension.

- `dirichletEtaExt_eq_dirichletEta`:
  `1 < re s → dirichletEtaExt s = dirichletEta s`
  — agreement with r267's LSeries-defined `dirichletEta` on the
  domain of absolute convergence, via r268.

- `dirichletEtaExt_apply`:
  `dirichletEtaExt s = (1 - (2 : ℂ)^(1 - s)) * riemannZeta s`
  — the defining equation packaged as a lemma for downstream `rw`.

## Route B substrate value

r269 gives us a first-class complex number `dirichletEtaExt (1/2 : ℂ)`
that both:
- equals `(1 - 2^{1/2}) · ζ(1/2) = (1 - √2) · ζ(1/2)` by definition
  (to be spelled out at s = 1/2 in r270), and
- equals `dirichletEta (1/2 : ℂ)` WHERE the LSeries makes sense
  (which is not at 1/2, but the extension avoids that issue by
  definition on all of ℂ).

Downstream:
- r270 specialises `dirichletEtaExt (1/2)` to `(1 - √2) · ζ(1/2)`.
- r271 matches with r265's real-valued `dirichletEtaHalf`.
- r272 inhabits the r266 conditional and closes Route B fact (a).

## Scope

* NOT novel — the extension by the classical identity is standard.
* NOT a Millennium discharge.
* IS the total-function bridge from r267's absolute-convergence
  `dirichletEta` to the value at s = 1/2 needed by r266.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.DirichletEtaZetaIdentity_r268

open scoped Real

namespace PrincipiaTractalis.DirichletEtaExtension

open Complex
open PrincipiaTractalis.DirichletEtaComplex
open PrincipiaTractalis.DirichletEtaZetaIdentity

/-! ## §1 The total extension. -/

/-- **`dirichletEtaExt`** — the extension of Dirichlet eta from its
LSeries-only domain `1 < re s` to all of `ℂ`, defined via the classical
identity `η(s) = (1 - 2^{1-s}) · ζ(s)`. This is a total complex function
because `riemannZeta` is total in mathlib. -/
noncomputable def dirichletEtaExt (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- **`dirichletEtaExt_apply`** — packaged form of the definition for
downstream `rw`. -/
lemma dirichletEtaExt_apply (s : ℂ) :
    dirichletEtaExt s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := rfl

/-! ## §2 Agreement with the LSeries-defined eta on `1 < re s`. -/

/-- **`dirichletEtaExt_eq_dirichletEta`** — on the domain of absolute
convergence `1 < re s`, the extension agrees with r267's LSeries-defined
`dirichletEta`. Via r268. -/
theorem dirichletEtaExt_eq_dirichletEta {s : ℂ} (hs : 1 < s.re) :
    dirichletEtaExt s = dirichletEta s := by
  rw [dirichletEtaExt_apply,
      ← dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta hs]

/-! ## §3 Axiom check. -/

#print axioms PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt_apply
#print axioms PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt_eq_dirichletEta

end PrincipiaTractalis.DirichletEtaExtension

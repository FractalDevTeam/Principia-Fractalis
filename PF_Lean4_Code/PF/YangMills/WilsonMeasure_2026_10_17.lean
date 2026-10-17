/-
# Yang-Mills — Wilson lattice measure on finite periodic Λ ⊂ (ℤ/L)⁴ (step 2)

**Rio's YM step 2, 2026-10-17** (codex `f85c078b`): with Haar on SU(2)
landed (`HaarSU2_2026_10_17.lean`, commit `a25ca2fa`), the Wilson lattice
measure follows definitionally — the measure exists because Haar exists.

### What this file provides

* `LatticeDir` = `Fin 4` — the four spacetime directions.
* `LatticeSite L` = `LatticeDir → Fin L` — a periodic 4-cube of side `L`.
* `LatticeLink L` = `LatticeSite L × LatticeDir` — oriented links.
* `Plaquette L` = `LatticeSite L × LatticeDir × LatticeDir` — the
  (base-point, μ, ν) data of an elementary 2-cycle.
* `GaugeField L` = `LatticeLink L → SU2` — assignment of SU(2) to each link.
* `shiftSite x μ` — periodic shift by 1 in direction μ.
* `plaquetteHolonomy U p` — `U(x,μ)·U(x+μ,ν)·U(x+ν,μ)⁻¹·U(x,ν)⁻¹ ∈ SU(2)`.
* `wilsonActionDensity U p` — `1 - (1/2)·Re tr(U_p)` (SU(2) plaquette action).
* `wilsonActionTotal U` — `Σ_p wilsonActionDensity U p` (continuous, bounded
  on the compact `GaugeField L`).
* `wilsonBaseMeasure L` — `Measure.pi (fun _ => SU2_haar)` — the uniform
  product measure. **Probability measure on `GaugeField L`.**
* `wilsonGibbsMeasure L β` — `exp(-β · S_W) · wilsonBaseMeasure L` (via
  `withDensity`). The Wilson probability-density measure at inverse
  coupling β (unnormalized; dividing by `Z` yields the Gibbs state).

### What this file does NOT prove

* `IsFiniteMeasure (wilsonGibbsMeasure L β)` — true on compact (bounded
  density on finite-measure base), but would require packaging continuity
  of the plaquette holonomy map; the measure object itself exists
  definitionally.
* Normalization `Z = ∫ exp(-β·S_W) dμ₀` — follows from the next bullet.
* Gauge invariance under left/right SU(2) action on each link — true,
  not proved here (not needed for reflection positivity).

### Three-axiom bar

Every declaration kernel-clean `[propext, Classical.choice, Quot.sound]`.
No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.YangMills.HaarSU2_2026_10_17
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false

namespace PF.YangMills

open Matrix MeasureTheory

noncomputable section

/-! ## §1 — Finite periodic 4-lattice. -/

/-- Lattice directions μ ∈ {0, 1, 2, 3}. -/
abbrev LatticeDir : Type := Fin 4

/-- Lattice sites in a periodic 4-cube of side `L`: a function from directions
to coordinates. -/
abbrev LatticeSite (L : ℕ) : Type := LatticeDir → Fin L

/-- Lattice links: (base site, outgoing direction). -/
abbrev LatticeLink (L : ℕ) : Type := LatticeSite L × LatticeDir

/-- Plaquette: (base site, μ, ν). The elementary 2-cycle starting at `x` in
the (μ, ν) plane. Diagonal (μ = ν) plaquettes contribute trivially and
need not be excluded. -/
abbrev Plaquette (L : ℕ) : Type := LatticeSite L × LatticeDir × LatticeDir

/-- A gauge-field configuration on the lattice: SU(2)-valued link variables. -/
abbrev GaugeField (L : ℕ) : Type := LatticeLink L → SU2

/-! ## §2 — Periodic translation on the lattice. -/

/-- Shift a lattice site by +1 in direction μ (periodic / modular). -/
def shiftSite {L : ℕ} [NeZero L] (x : LatticeSite L) (μ : LatticeDir) :
    LatticeSite L :=
  Function.update x μ (x μ + 1)

/-! ## §3 — Plaquette holonomy. -/

/-- The plaquette holonomy
`U_p = U(x, μ) · U(x + μ̂, ν) · U(x + ν̂, μ)⁻¹ · U(x, ν)⁻¹ ∈ SU(2)`.
Takes values in `SU(2)` (closed under multiplication and inverse). -/
def plaquetteHolonomy {L : ℕ} [NeZero L] (U : GaugeField L) (p : Plaquette L) :
    SU2 :=
  U (p.1, p.2.1) *
    U (shiftSite p.1 p.2.1, p.2.2) *
    (U (shiftSite p.1 p.2.2, p.2.1))⁻¹ *
    (U (p.1, p.2.2))⁻¹

/-! ## §4 — Wilson action. -/

/-- Wilson action density per plaquette for SU(2):
`S_p(U) = 1 - (1/2) · Re(tr U_p)`.
The constant `1/2 = 1/N` for `N = 2`; replaced by `1/N` in general SU(N). -/
def wilsonActionDensity {L : ℕ} [NeZero L] (U : GaugeField L) (p : Plaquette L) :
    ℝ :=
  1 - (1/2) * ((plaquetteHolonomy U p : Matrix (Fin 2) (Fin 2) ℂ).trace.re)

/-- Total Wilson action: sum over all plaquettes.
`S_W(U) = Σ_{p plaquette} S_p(U)`. -/
def wilsonActionTotal {L : ℕ} [NeZero L] (U : GaugeField L) : ℝ :=
  ∑ p : Plaquette L, wilsonActionDensity U p

/-! ## §5 — The Wilson base measure (uniform Haar product). -/

/-- **The uniform base measure on gauge-field configurations**:
`μ₀ = ⊗_{ℓ ∈ links} haar_{SU(2)}` — Haar on each link, independent across
links. Via `Measure.pi` on the finite index set `LatticeLink L`. -/
def wilsonBaseMeasure (L : ℕ) [NeZero L] : Measure (GaugeField L) :=
  Measure.pi (fun _ : LatticeLink L => SU2_haar)

/-- **`wilsonBaseMeasure L` is a probability measure** — product of
probability measures (`SU2_haar`) on a finite index set. -/
instance wilsonBaseMeasure_isProbabilityMeasure (L : ℕ) [NeZero L] :
    IsProbabilityMeasure (wilsonBaseMeasure L) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.pi (fun _ : LatticeLink L => SU2_haar)))

/-! ## §6 — The Wilson Gibbs measure. -/

/-- **★ Wilson Gibbs measure at inverse coupling β ★** —
`μ_β = exp(-β · S_W(U)) · μ₀`.
The unnormalized Gibbs measure; the normalized state is `μ_β / Z` where
`Z = μ_β(univ) = ∫ exp(-β S_W) dμ₀` is the partition function.

Exists definitionally — Haar on SU(2) gives `μ₀`, and `withDensity`
produces the weighted measure. -/
def wilsonGibbsMeasure (L : ℕ) [NeZero L] (β : ℝ) : Measure (GaugeField L) :=
  (wilsonBaseMeasure L).withDensity
    (fun U => ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U)))

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.shiftSite
#print axioms PF.YangMills.plaquetteHolonomy
#print axioms PF.YangMills.wilsonActionDensity
#print axioms PF.YangMills.wilsonActionTotal
#print axioms PF.YangMills.wilsonBaseMeasure
#print axioms PF.YangMills.wilsonBaseMeasure_isProbabilityMeasure
#print axioms PF.YangMills.wilsonGibbsMeasure

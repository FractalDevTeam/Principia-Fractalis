import PF.SpectralGap

namespace PF_L4L.Core

open PrincipiaTractalis

/--
PF_L4L core specification for the P vs NP spectral gap. This record
packages the ground state energies and the spectral gap together with
basic numerical properties, and we instantiate it using the canonical
PF theorems.
-/
structure SpectralGapSpec where
  lambda0P : ℝ
  lambda0NP : ℝ
  gap : ℝ
  gap_def : gap = lambda0P - lambda0NP
  gap_positive : gap > 0
  gap_approx : |gap - 0.0539677287| < 1e-8

noncomputable def spectralGapSpecPF : SpectralGapSpec :=
  { lambda0P := lambda_0_P
  , lambda0NP := lambda_0_NP
  , gap := spectral_gap
  , gap_def := rfl
  , gap_positive := spectral_gap_positive
  , gap_approx := spectral_gap_value }

@[simp] theorem spectralGapSpecPF_gap :
    spectralGapSpecPF.gap = spectral_gap := rfl

@[simp] theorem spectralGapSpecPF_lambda0P :
    spectralGapSpecPF.lambda0P = lambda_0_P := rfl

@[simp] theorem spectralGapSpecPF_lambda0NP :
    spectralGapSpecPF.lambda0NP = lambda_0_NP := rfl

end PF_L4L.Core

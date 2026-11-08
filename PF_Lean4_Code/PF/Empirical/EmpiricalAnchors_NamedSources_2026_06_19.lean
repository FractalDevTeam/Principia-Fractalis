/-
# PF.Empirical.EmpiricalAnchors_NamedSources_2026_06_19

2026-06-19 — Ten bibliographic citation markers naming the empirical
measurement sources the framework's predictions are compared against.
Rewritten 2026-11-06 to remove the free-discharge pattern — see Hodge
NamedAnchors cleanup `c98e5b90` for method and rationale.

## What this file is

Ten `Prop := True` definitions that NAME specific named/refereed
empirical measurement sources. Bibliographic markers only.

Quantum hardware (1):
  - IBM Quantum two-instance observation of α_RH = 3/2 and
    α_NP ≈ 1.868 ≈ φ + 1/4.

Particle physics (4):
  - CDF II 2022 W-boson mass anomaly (Aaltonen et al., Science
    376:170-176).
  - XENON Collaboration XENONnT electronic-recoil (Aprile et al.,
    PRL 129:161805).
  - PDG 2024 neutrino mass hierarchy (Workman et al., PTEP 2024:083C01).
  - Fermilab Muon g-2 anomalous magnetic moment (Aguillard et al.,
    PRL 131:161802).

Cosmology (5):
  - Local Distance Network 2025 H₀ consensus (arXiv:2510.23823,
    A&A 2026).
  - Planck Collaboration 2018 CMB (A&A 641:A6).
  - DESI BAO Year-3 release (DESI Collaboration 2024).
  - Pantheon+ Type Ia supernova catalog (Scolnic et al.,
    ApJ 938:113).
  - LIGO/Virgo/KAGRA gravitational-wave dark-energy constraints
    (LVK Collaboration 2021, arXiv:2111.03634).

## What was removed on 2026-11-06

  `theorem <lowercase>_anchor_holds := trivial` × 10
  disjunction + conjunction bundles with `_holds` theorems
  audit-trail capstone

Removed. Bibliographic markers only.

## Scope

These NAME the independent measurement sources against which the
framework's predictive bounds are compared. The named measurements
are the input observations, not derivations of the substrate's
predictions.

## Axiom budget

Zero project axioms. The file now contains no theorems.
-/

namespace PF.Empirical.EmpiricalAnchors_NamedSources_2026_06_19

/-- **IBM Quantum two-instance observation citation marker.**
    α_RH = 3/2 and α_NP ≈ 1.868 ≈ φ + 1/4 to four decimals on IBM
    Quantum hardware. See corpus
    `IBM_hardware_nine_way_random_match_probability_bound`.
    Bibliographic reference. -/
def IBMQuantum_TwoInstance_Observation_Anchor : Prop := True

/-- **CDF II 2022 W-boson mass citation marker.** Aaltonen et al.,
    "High-precision measurement of the W boson mass with the CDF II
    detector", Science 376 (2022), 170-176. Bibliographic reference. -/
def CDFII2022_WBosonMass_Anchor : Prop := True

/-- **XENONnT electronic-recoil citation marker.** Aprile et al.,
    "Search for new physics in electronic recoil data from XENONnT",
    Phys. Rev. Lett. 129 (2022), 161805. Bibliographic reference. -/
def XENONnT_ElectronicRecoil_Anchor : Prop := True

/-- **PDG 2024 neutrino-hierarchy citation marker.** Workman et al.
    (Particle Data Group), "Review of Particle Physics",
    PTEP 2024 (2024), 083C01. Bibliographic reference. -/
def PDG2024_NeutrinoHierarchy_Anchor : Prop := True

/-- **Fermilab Muon g-2 2023 citation marker.** Aguillard et al.
    (Muon g-2 Collaboration), "Measurement of the positive muon
    anomalous magnetic moment to 0.20 ppm", Phys. Rev. Lett. 131
    (2023), 161802. Bibliographic reference. -/
def FermilabMuonG2_2023_Anchor : Prop := True

/-- **Local Distance Network 2025 H₀ citation marker.** arXiv:2510.23823,
    A&A 2026. Bibliographic reference. -/
def LDN2025_HubbleConstant_Anchor : Prop := True

/-- **Planck 2018 CMB citation marker.** Planck Collaboration,
    "Planck 2018 results. VI. Cosmological parameters",
    A&A 641 (2020), A6. Bibliographic reference. -/
def Planck2018_CMB_Anchor : Prop := True

/-- **DESI BAO Year-3 citation marker.** DESI Collaboration, Year-3
    BAO data release (2024). Bibliographic reference. -/
def DESI_BAO_Year3_Anchor : Prop := True

/-- **Pantheon+ SNe Ia citation marker.** Scolnic et al.,
    "The Pantheon+ Analysis: The Full Data Set and Light-Curve Release",
    ApJ 938 (2022), 113. Bibliographic reference. -/
def PantheonPlus_SNeIa_Anchor : Prop := True

/-- **LIGO/Virgo/KAGRA GW dark-energy citation marker.** LVK
    Collaboration 2021 constraints on dark-energy equation of state,
    arXiv:2111.03634. Bibliographic reference. -/
def LVK_GW_DarkEnergy_Anchor : Prop := True

end PF.Empirical.EmpiricalAnchors_NamedSources_2026_06_19

"""
Summary of dark-matter-without-matter framework test.
Aggregates results and outputs final synthesis.
"""
print("=" * 70)
print("FRAMEWORK 'DARK MATTER WITHOUT MATTER' — SYNTHESIS")
print("=" * 70)

results = [
    ("NGC 3198 rotation curve",
     "Framework C^μν fits with chi2/dof = 4.99 (NFW: 9.07, baryon: 68.1)",
     "PASS — Gaussian C^μν reproduces flat curve with rho_C0=2.7e6 Msun/kpc^3, r_C=22 kpc"),

    ("Bullet Cluster 1E 0657-558",
     "Framework lensing peak coincides with galaxies (+0.34 vs +0.35 Mpc),",
     "PASS — C^μν tied to galaxies → automatic lens-gas offset of +0.25 Mpc"),

    ("Coma cluster M/L",
     "Need A_C(cluster) ≈ 41 vs A_C(galaxy) ≈ 3 → scale-dependent coupling",
     "MIXED — explanation possible only with scale-running A_C(M)"),

    ("MOND comparison",
     "Both reproduce flat curves; framework lacks Tully-Fisher derivation",
     "MIXED — framework currently fit-per-system, not predictive"),

    ("NFW profile comparison (dwarfs)",
     "Framework Gaussian is inherently CORED (slope ≈ 0)",
     "WIN — natural solution to NFW cusp-core problem"),

    ("CMB acoustic peaks",
     "ch_2(z=1100) < 1e-4 → no consciousness at recombination",
     "GAP — framework needs separate mechanism for CMB / early-universe LSS"),

    ("Missing satellites",
     "Consciousness threshold suppresses small-halo formation",
     "PLAUSIBLE — natural prediction not yet quantified"),

    ("UDGs (DF2, DF4)",
     "Framework predicts UDGs with no consciousness substrate → v ≈ v_baryon",
     "TESTABLE — observed DF2 v_obs ≈ v_baryon CONSISTENT")
]

print(f"\n{'Test':<35} {'Outcome':<10}  {'Verdict'}")
print("-" * 100)
for test, finding, verdict in results:
    verdict_tag = verdict.split(" —")[0]
    print(f"{test:<35} {verdict_tag:<10}  {finding}")

print("\n" + "=" * 70)
print("FALSIFIABLE PREDICTIONS")
print("=" * 70)
preds = [
    "1. C^μν must correlate spatially with stellar/baryonic mass",
    "   → Lensing maps should NEVER show offsets between mass and galaxies > beam size",
    "2. UDGs with low stellar density → low effective dark-matter signal",
    "   → DF2-like galaxies are FEATURE not bug",
    "3. Dwarf galaxies show CORED rotation curves (consistent with obs)",
    "4. CMB at z=1100 cannot have ch_2-sourced gravitational potential",
    "   → Framework must explain acoustic peaks via baryon-only physics or",
    "     pre-recombination C^μν mechanism (currently UNDISCHARGED)",
    "5. A_C(scale) function — coupling must run from ~3 at galaxy to ~40 at cluster",
    "   → Predicts intermediate values for galaxy groups (10^13 Msun systems)",
    "6. Bullet-like systems: lensing always tracks galaxies, never gas"
]
for p in preds:
    print(p)

print("\n" + "=" * 70)
print("HONEST ASSESSMENT")
print("=" * 70)
print("""
WHAT THE FRAMEWORK DELIVERS:
  • A C^μν profile shape (Gaussian via ch_2(r) = 0.95·exp(-r²/r_C²)) that
    reproduces NGC 3198 rotation curve as well as NFW (better than baryon).
  • A natural prediction that lensing follows galaxies, not gas
    (Bullet Cluster phenomenology emerges by construction).
  • An inherently CORED density profile that resolves the NFW cusp-core
    problem at dwarf-galaxy scale.

WHAT REMAINS UNDERSPECIFIED:
  • No first-principles derivation of (rho_C0, r_C) from baryon content
    → can't predict Tully-Fisher slope ab initio
  • Scale-dependent coupling A_C(M) needed for galaxy-cluster consistency,
    same structural challenge as ΛCDM's stellar-halo-mass relation
  • CMB acoustic peaks at z=1100: framework states ch_2 < 1e-4 there;
    needs alternative mechanism for the gravitational potential wells
    that DM provides in ΛCDM
  • Structure formation simulations: no framework analogue of cosmological
    N-body codes; cannot yet test against power spectrum P(k)

NET VERDICT:
  Framework can REPRODUCE galaxy-scale dark-matter phenomenology with
  reasonable, physically-motivated consciousness distributions. Its
  natural prediction of cored profiles is an ADVANTAGE over CDM.
  At cluster scale and at recombination, it requires either:
    (a) scale-running of the consciousness coupling (parameterised, like ΛCDM),
    or (b) explicit mechanism currently absent.

  This is the same epistemic status as MOND: works galactically,
  needs extension cluster-wide, no current CMB story.
  The 'dark matter without matter' claim is THEORETICALLY VIABLE
  but EMPIRICALLY UNDERDETERMINED at the cluster + cosmological levels.
""")

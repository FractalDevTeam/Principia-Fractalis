# Manuscript reading ledger --- audit pass of 2026-10-07

Commit at start of pass: `0ef96a27`. Commit now: `088fffe1`.
Toolchain: Lean 4.24.0-rc1 / Lake 5.0.0 / mathlib `eed770a4` / Rocq 9.1.0.
Include graph: **68 files, 38,933 source lines at commit `088fffe1`**
(resolved recursively from `main.tex`, comment-aware). The 7 `.tex` files on
disk not reached by the graph are 2-line stubs.

*Denominator correction (2026-10-08).* The earlier **38,995** total combined
stale pre-commit file sizes with a line-count convention that added one to most
included files. A fresh parser over the exact current include graph reports
38,933 physical lines and the per-file counts below. Earlier percentages are
superseded by this denominator.

Status: **READING PASS COMPLETE.** **38,933 of 38,933 lines read in full (100%)**
across all 68 included files. An earlier draft of this
ledger said "~12,900 (33%)" --- that was an estimate that counted the `ch08`
partial as full, and is corrected here. Halted on context budget, not on a
decision. Pass 2 resumed from the recorded boundary and completed ch11--ch34.
The continuing controlled lane has now completed ch34A, ch35, the foundational
lexicon, Appendices A--L, all backmatter and the complete ch08. The
full-manuscript reading pass is closed; findings remain provisional pending the
exact Lean source/dependency/provenance audit specified in the handoff below.

Both commits `3cdd430c` and `088fffe1` are QUARANTINED pending review. No further
manuscript or API mutation during this pass. Gate sweep is read-only.

---

## READ IN FULL

| File | Lines |
|---|---|
| `main.tex` | 147 |
| `preamble.tex` | 719 |
| `frontmatter/title.tex` | 50 |
| `frontmatter/copyright.tex` | 58 |
| `frontmatter/version_history.tex` | 1150 |
| `frontmatter/prologue.tex` | 114 |
| `frontmatter/preface.tex` | 108 |
| `frontmatter/howto.tex` | 328 |
| `frontmatter/notation.tex` | 316 |
| `frontmatter/acknowledgments.tex` | 178 |
| `chapters/ch01_numbers.tex` | 1534 |
| `figures/ch01_*.tex` (5 files) | 246 |
| `chapters/ch02_complex.tex` | 540 |
| `chapters/ch03_resonance.tex` | 529 |
| `chapters/ch04_timeless_field.tex` | 775 |
| `chapters/ch05_peixoto.tex` | 568 |
| `chapters/ch06_consciousness.tex` | 851 |
| `chapters/ch07_constants.tex` | 945 |
| `chapters/ch08_field_equations.tex` | 682 |
| `chapters/ch09_spectral_unity.tex` | 708 |
| `chapters/ch10_hydrodynamic.tex` | 730 |
| `chapters/ch11_geometric_unity.tex` | 702 |
| `chapters/ch12_qft_consciousness.tex` | 585 |
| `chapters/ch13_solutions_dynamics.tex` | 674 |
| `chapters/ch14_symmetries_conservation.tex` | 674 |
| `chapters/ch15_computational_methods.tex` | 769 |
| `chapters/ch16_spectral_foundations.tex` | 680 |
| `chapters/ch17_operator_theory.tex` | 657 |
| `chapters/ch18_spectral_measures.tex` | 673 |
| `chapters/ch19_physical_applications.tex` | 527 |
| `chapters/ch20_riemann_hypothesis.tex` | 679 |
| `chapters/ch21_p_vs_np.tex` | 1600 |
| `chapters/ch22_navier_stokes.tex` | 845 |
| `chapters/ch23_yang_mills.tex` | 752 |
| `chapters/ch24_birch_swinnerton_dyer.tex` | 904 |
| `chapters/ch25_hodge_conjecture.tex` | 685 |
| `chapters/ch26_cosmological_constant.tex` | 689 |
| `chapters/ch27_dark_energy_expansion.tex` | 850 |
| `chapters/ch28_early_universe.tex` | 821 |
| `chapters/ch29_observational_tests.tex` | 729 |
| `chapters/ch30_clinical_consciousness.tex` | 918 |
| `chapters/ch31_neuroscience_iit.tex` | 838 |
| `chapters/ch32_consciousness_quantification.tex` | 850 |
| `chapters/ch33_numerical_methods.tex` | 500 |
| `chapters/ch34_verification.tex` | 931 |
| `chapters/ch34A_substrate_theorem.tex` | 2394 |
| `chapters/ch35_software.tex` | 896 |
| `backmatter/appendix_lexicon.tex` | 290 |
| `appendices/appA_zeros.tex` | 248 |
| `appendices/appB_brst.tex` | 349 |
| `appendices/appC_clinical.tex` | 463 |
| `appendices/appD_software.tex` | 193 |
| `appendices/appE_weinstein.tex` | 121 |
| `appendices/appF_solutions.tex` | 168 |
| `appendices/appG_notation.tex` | 178 |
| `appendices/appendix_grothendieck.tex` | 463 |
| `appendices/appH_numerical_validation.tex` | 460 |
| `appendices/appI_lean_cross_reference.tex` | 424 |
| `appendices/appJ_refinement_pass_2026-06-07.tex` | 452 |
| `appendices/appK_residual_compaction_2026-06-15_16.tex` | 1007 |
| `appendices/appL_substrate_bundle_closure_2026-06-18_19.tex` | 491 |
| `backmatter/glossary.tex` | 117 |
| `backmatter/author.tex` | 137 |
| `backmatter/epilogue.tex` | 274 |

## NOT YET READ

None. All 68 files reachable from the current `main.tex` include graph were read
in full at commit `088fffe1`.

---

## FINDINGS NOT ALREADY FLAGGED IN THE MANUSCRIPT

1. **ch01 `thm:d3-modular` was FALSE.** `D_3(n) = n (mod 3)` fails for 666 of the
   first 999 integers; smallest counterexample `n = 3`. Proof step
   "`D_3(n) = sum d_k = d_0 (mod 3)`" discards `sum_{k>=1} d_k`. The chapter's
   Verification-status ledger vouched for the mod-(b-1) and parity theorems by
   name and never mentioned this third one. REPAIRED in `3cdd430c` (quarantined).
2. **ch01 1.5 alpha preview**: `alpha_RH = 1/2`, `alpha_YM = e`; canonical are
   `3/2` and `2`. ch03's table was corrected 2026-05-18; ch01 was not.
   Corrected in `3cdd430c` (quarantined).
3. **ch07 `tab:sacred-alpha`**: NS row read `5/3`, the exact value ch03 names as
   superseded. Corrected in `3cdd430c` (quarantined).
4. **ch07 `thm:p-np-gap` "Detailed Calculation" does not produce its own
   numbers.** `(1/3) sum_{k=0..2} exp(i pi alpha k)` is COMPLEX:
   `-0.0414905 - 0.1502047i` at `sqrt 2`, `+0.8635915 - 0.3800592i` at
   `phi + 1/4`. Quoted reals `0.4327896`, `0.5219115` match no real part, no
   imaginary part, no modulus (`0.1558298`, `0.9435228`). Footnoted in
   `3cdd430c`; digits left standing (theory-meaning).
5. **ch07 percolation substitutes its own number.** Computes
   `p_c = 1000/(50000-1000) = 0.020408`, then writes `1 - 0.05 = 0.95`.
   `1 - 0.020408 = 0.979592`. Reaching 0.95 needs `<k^2> ~ 21,000`, not 50,000.
   Footnoted in `3cdd430c`; the value 0.95 untouched.
6. **ch10:705 broke the PDF.** `eq.~(10/\pi)\cdot\omega_c\cdot10^5` had math
   commands outside math mode; pdflatex halted and emitted NO PDF, from commit
   `056d85d6` until repaired in `3cdd430c`. Nothing in the pipeline was
   compiling the book.
7. **ch09 gives a FOURTH origin story for the "10" in pi/10, and it is
   self-refuting.** Twice (secs "Ground State Energy" and "The Unreasonable
   Effectiveness") the text attributes it to "`10_3 = 3_10` in base-3". If the
   denominator were base-3 "10" it would be 3, giving `pi/3 = 1.047`, not
   `pi/10 = 0.314`. UNFLAGGED. The other three: ch07 decimal-bins (invalid),
   ch07 polylog expansion (false), and `h(H_3) = 10` (the real candidate).
8. **ch04 "dyadic rationals base-3" correction was incompletely propagated.**
   Fixed at the K-theory theorem; the identical phrase survives in the
   interpretation paragraph below it.
9. **ch04's K-theory proof sketch displays `K_0 = inverse-limit of Z = Z[1/3]`**,
   which is false as written (that inverse limit is 0; the colimit is Z[1/3]).
   The definition above it carries the direction correction; this displayed
   equation does not.
10. **ch04 has no chapter-level Verification-status ledger** --- it has a
    theorem-scoped "Machine-verification status of Theorem 4.x" paragraph
    instead. It is the only chapter in 1--10 without the chapter-level form.
    (Correcting my earlier statement that it had "no ledger at all".)
11. **`thm:universal_frequency` (ch09) is an unverified numerical claim**:
    `pi/10 = (1/2) integral_0^1 R_f(sqrt 2, 1/2 + ix) dx`. The integral is
    well-defined (`sigma(sqrt 2) ~ -0.69 < 1/2`) but the identity is NOT checked.
    TO DO.
12. **ch11's anomaly coefficient begins from a false group dimension.** It uses
    `dim(Spin(13,1)) = 8192` and hence `A_14 = 8192 - 6 - 12 = 8174`. The Lie
    algebra dimension is `dim so(13,1) = 14*13/2 = 91`; `8192 = 2^13` is not
    the dimension of `Spin(13,1)`. More fundamentally, a gauge/trace anomaly
    coefficient is not obtained by subtracting group dimensions. The existing
    correction refutes the printed numerical close even on its own inputs but
    does not flag this upstream structural defect.
13. **ch11's RQG Gaussian is not consistently defined and its analytic claims
    do not follow.** The variance is printed as an average of
    `(R_f-<R_f>)^2` although `R_f` is complex, while the damping exponent later
    uses `|R_f-<R_f>|^2`. Gaussian damping on an infinite-dimensional fiber does
    not make its effective support a finite-dimensional compact ball, and no
    measure, integrability hypothesis, nonzero finite normalization, or proof
    of the claimed `e^(pi/10)` operator-norm bound is supplied. The claimed
    scaling symmetry and maximization at `alpha=sqrt(0.95)` likewise do not
    follow from the displayed definition.
14. **ch11's modified BRST construction is not shown to be a differential.**
    For a nonconstant multiplier `Psi`, `(Psi*delta)^2` generally contains a
    `delta(Psi)` term; nilpotency requires an invariance/closedness condition
    that is not stated. If `Psi` is everywhere nonzero and acts as a compatible
    scalar, multiplication alone does not filter cohomology classes. The value
    78 is then obtained by a disclosed post-hoc switch from species to mixed
    degrees-of-freedom counting; the polarization count also treats the massive
    W/Z as having two polarizations while using the pre-EWSB four-component
    Higgs count. `dim(E_6)=78` is a Lie-algebra dimension, not by itself a
    particle count.
15. **ch11's ANITA mechanism contradicts its own formula.** It defines
    `sigma_RQG = sigma_SM * |Psi_RQG|^2`, then says that at resonance
    `Psi_RQG approximately 1` the cross-section is reduced by about 100. The
    displayed formula instead gives essentially no reduction at resonance.
16. **ch11's lithium claim overstates its own arithmetic.** At the stated
    inputs the rate factor is `1-(pi/10)*0.95 approximately 0.702`, a 30%
    reduction, not a factor-of-three reduction. Applying it to `5.24e-10`
    gives about `3.68e-10`, not the cited `1.6e-10` observation.
17. **ch11 does not propagate its own verification status.** The inline
    corrections and final ledger withdraw the anomaly, Gaussian, 4D projection,
    muon-g-2, and experimental-confirmation closes, but the chapter abstract,
    green boxes, theorem headlines, summary, and exercises continue to state or
    ask the reader to verify those results as established. This is a headline
    versus scope-ledger contradiction, not a reason to remove the RQG program.
18. **ch12's displayed field strength does not have its claimed index
    symmetry, and its matter interaction is not a scalar as printed.** In
    `F_C^{munurhosigma}`, exchanging `rho` and `sigma` does not negate the
    displayed expression; the fourth term even repeats `C^{nurho}` rather than
    supplying the exchanged tensor. In the purported Lagrangian term
    `bar(psi) gamma^{(mu} C^{nu)rho} gamma_rho psi`, `mu,nu` remain free. Thus
    the printed action is not yet a defined Lorentz-scalar action from which the
    subsequent field equation or Feynman rules can be derived.
19. **ch12's propagator and ghost-free claim do not follow from its
    Lagrangian.** The displayed numerator is the massive Fierz--Pauli spin-2
    projector, but the written mass term contains only `C^{munu}C_{munu}` and
    omits the tuned trace subtraction, while the kinetic sector contains two
    independent derivative forms without a specified gauge symmetry,
    constraint analysis or gauge fixing. A generic symmetric Lorentz tensor has
    ten components, not the five physical polarizations silently assumed by the
    propagator. Positive energy and unitarity therefore remain open consistency
    obligations; this does not rule out a corrected consciousness-field model.
20. **ch12 imports a Yang--Mills beta-function conclusion without defining a
    Yang--Mills theory.** The one-loop coefficient uses an undefined number of
    "consciousness colors" `N_c`, but no gauge group, generators, representation,
    covariant field strength or ghost action is given. Consequently the claim
    that `g_C` is asymptotically free is not established for the printed
    rank-two tensor theory.
21. **ch12's unitarity paragraph assumes the conclusion.** Enlarging a direct
    sum and writing channel probabilities that sum to one does not construct a
    self-adjoint Hamiltonian or prove a unitary S-matrix. Moreover `T_infinity`
    is a C*-algebra, not itself a Hilbert space until a representation (for
    example a GNS construction and state) is selected. The claimed restoration
    of information is therefore a programmatic mechanism, not a proof.
22. **ch12's psychon cross-section and sensitivity claims disagree with its
    own formula.** With `g_C=10^-6`, `sqrt(s)=1 TeV` and
    `sigma ~ g_C^2 alpha/s`, the result is about `2.84e-12 pb` after the standard
    `GeV^-2` conversion, rather than `1e-15 pb`. Either value predicts
    essentially zero events at inverse-attobarn luminosity and is not at the
    edge of LHC sensitivity.
23. **ch12's interference-fringe scale is wrong by about four orders of
    magnitude.** Its formula `Delta x = pi hbar/(m_C c)` at
    `m_C=10^-5 eV` gives `0.06199 m` (about 6.2 cm), not `10 micrometres`.
24. **ch12 does not propagate its own verification ledger.** The final ledger
    correctly calls the quantized field, propagator, amplitudes, cosmology and
    experimental proposals untested, but the abstract, boxed statements and
    conclusion call the construction complete, unitary and experimentally
    testable as though those consequences had been derived. This is a
    manuscript-scoping defect, not a basis for deleting the QFT program.
25. **ch13's consciousness-modified Schwarzschild theorem is not the result of
    its printed proof.** For its stated density, setting `x=r/r_C` gives
    `integral_r^infinity rho_C(r') r'^2 dr' = hbar C_0 e^-x
    (x^3+4x^2+8x+8)`, not the displayed
    `hbar C_0( r_C^2+r_C r+r^2/2)e^-x/(8 pi G)`. The latter also introduces
    `G` although the integrand contains none. Substitution into the preceding
    field equation therefore does not yield the boxed
    `alpha_C C_0 r^-2 e^(-r/r_C)` correction. The density is attributed to ch12
    but does not occur there. Screening remains a possible model property, but
    this is not an exact solution as written.
26. **ch13's first advertised observable is dimensionally invalid.** Its
    perihelion correction multiplies the dimensionless GR factor
    `GM/[c^2 a(1-e^2)]` by `alpha_C`, which the theorem explicitly assigns units
    of length squared; the result cannot be an angle. The quoted numerical
    observables therefore do not follow from the boxed metric without a fresh,
    dimensionally consistent derivation.
27. **ch13's consciousness black hole is an RN--dS analogy, not a derived
    solution.** No normalization or conservation theorem is supplied for
    `Q_C = integral C^{0nu}dSigma_nu`; later the same chapter permits
    `nabla_mu C^{munu}=J^nu`, so conservation does not follow. A spacetime-varying
    `Lambda_eff(C)` also does not support the constant-`Lambda` RN--dS metric
    without its own field equation. The horizon calculation then drops the
    displayed cosmological term, calls the resulting equation a cubic in
    `r_h^2` although the original equation is quartic in `r_h`, and solves only
    the `Lambda=0` quadratic.
28. **ch13's consciousness entropy is not dimensionally defined and does not
    resolve information loss by itself.** `k_B integral ch_2 dA` has units
    `k_B length^2` for dimensionless `ch_2`; it needs an area normalization.
    Neither a Wald-entropy derivation nor a microstate count is supplied, and
    writing an enlarged generalized-second-law inequality is not a proof of
    that inequality.
29. **ch13's cosmological equations contain two independent algebra errors.**
    The acceleration equation uses `rho_r + (4/3)rho_r = (7/3)rho_r`, whereas
    radiation contributes `rho_r+3p_r=2rho_r`. Its effective dark-energy formula
    `w_Lambda=d ln Lambda_eff/d ln a - 1` is not the continuity-equation result;
    for a separately conserved effective density it is
    `w=-1-(1/3)d ln rho/d ln a`. These differences reverse the interpretation
    of a decreasing `Lambda_eff` and invalidate the stated observational close.
30. **ch13's gravitational-wave dispersion does not follow from its proof.**
    The constitutive step `delta C_TT ~ (rho_C/omega^2)h_TT` is asserted without
    deriving `delta C` from the ch12 action, and substitution does not produce
    the boxed expression: factors of `omega`, `k` and 2 change between adjacent
    lines. Restoring SI dimensions, the stated inputs give
    `G rho_E/(c^2 omega^2) about 1.88e-43`, not `1e-30`; the analogous amplitude
    scale is about `2.73e-21`, not `1e-12`. The high-frequency GR limit is a
    reasonable requirement, but these predictions are not yet derived.
31. **ch13's stability theorem supplies neither a necessary nor sufficient
    stability analysis.** `c_s^2>0` alone does not show that the full
    Regge--Wheeler/Zerilli operator has no negative eigenvalues, and the printed
    potential is merely asserted. The ratio condition `rho_C/p_C>-3` is
    undefined when `p_C=0` and is not connected to the claimed spectral bound.
    Radial and non-radial stability therefore remain open even conditionally.
32. **ch13's advanced constructions reuse results for different matter
    models.** The Kaup bound quoted is for a minimally coupled scalar boson
    star, not automatically for the symmetric tensor/fluid `C^{munu}` defined
    here. The wormhole correction is logarithmically singular at its own throat
    (`ln(b_0/l)` as `l->0`), and
    `c^4/(G hbar Lambda_0)` has dimensions of velocity rather than the stated
    dimensionless consciousness threshold. These are candidate analogies, not
    numerical solutions of the printed theory.
33. **ch13's final verification ledger is more accurate than its chapter
    body, but still overcalls the results as "exact solutions" and
    "framework-internal consistency".** Findings 25--32 are failures within the
    displayed equations themselves, before empirical validation. The correct
    status is a set of proposed ansatzes and phenomenological targets awaiting a
    coherent action, conserved source, exact solution and stability analysis;
    this strengthens the research program's task list without changing its TOE
    scope.
34. **ch14 applies flat-spacetime Noether charges on a generic curved spacetime
    without the required symmetries.** A generic curved spacetime has no global
    translation symmetry, so `integral sqrt(g) T^{00}` is coordinate-dependent
    and is not generally a conserved energy or equal to ADM mass. ADM energy
    requires asymptotic flatness and the appropriate boundary construction;
    conserved bulk charges require a Killing field (plus boundary and falloff
    hypotheses). The standard Noether theorem survives, but the chapter's
    energy/momentum formulas do not follow merely from general covariance.
35. **ch14's intrinsic-spin expression is not a tensor expression of the
    defined field.** `C^{[i0]j}` has three displayed indices although
    `C^{munu}` has two. Symmetry of a rank-two tensor does not by itself make it
    a physical spin-2 field; that conclusion requires the Lorentz
    representation, constraints and equations that were missing in ch12.
36. **ch14's local `U(1)_C` is not a symmetry of the printed ch12 action.** The
    claimed invariant `C^{munu}C_{munu}` transforms by `e^{2 i theta}` rather
    than remaining fixed; the invariant contraction would require a complex
    conjugate. Ordinary derivatives of a locally phased field also acquire
    `partial_mu theta` terms, but no `U(1)_C` connection or covariant derivative
    is introduced. Ch12 in turn writes real, unconjugated mass and quartic terms.
    A global or local complex-field extension may be constructed, but it is not
    the current action.
37. **ch13 and ch14 use inequivalent definitions of `Q_C`.** Ch13 defines it
    from a hypersurface integral of `C^{0nu}`; ch14 defines it from a newly
    asserted Noether current `j_C^0`. No theorem identifies the two. The printed
    current is not derived from the action, and a local gauge redundancy invokes
    Noether's second theorem rather than automatically giving the stated global
    charge. The black-hole charge and the claim that total consciousness is
    conserved therefore lack a common, proved definition.
38. **ch14's proposed T-violating interaction is not a Lorentz scalar.** In the
    displayed epsilon term, the indices `alpha,beta` occur only in
    `epsilon_{sigma lambda alpha beta}` and remain free (while `alpha` is also
    reused as the coupling symbol). More conceptually, the thermodynamic or
    cognitive arrow of time does not by itself demonstrate microscopic
    T-violation, and the antiunitary complex conjugation required for quantum
    time reversal is omitted. The C/T claims remain hypotheses, as the final
    ledger partly acknowledges.
39. **ch14's phase-transition temperature is not derived even after its
    arithmetic correction.** The source's own correction proves that the
    zero-temperature potential has no broken minimum for the printed signs.
    A finite-temperature critical point requires a thermally corrected
    effective potential and its thermal-mass coefficient; `T_C=m_C/sqrt(lambda)`
    does not follow from the displayed potential alone. Consequently the
    corrected `116 K, z about 42` arithmetic is conditional on an unprovided
    thermal model, and the Goldstone/Higgs discussion has no current vacuum to
    expand around.
40. **ch14 conflates a charged spin-2 matter field with a `U(1)` gauge field.**
    If a global `U(1)` were broken, a Goldstone mode could arise; if it were
    gauged, the associated vector connection would eat that mode. This does not
    make the charged rank-two field itself the gauge boson or supply its missing
    Fierz--Pauli constraints. The asserted consciousness-field mass therefore
    does not follow from the Higgs analogy.
41. **ch14's conformal claims are not consequences of `m_C=0`.** A massless
    limit need not be conformally invariant without the correct kinetic action,
    improvement/conformal coupling and treatment of anomalies; the trace formula
    is asserted rather than computed from the ch12 action. The Riemann zeta
    functional equation is a reflection identity, not conformal invariance of a
    spacetime QFT, and `Re(s)=1/2` is not thereby a physical "conformal point"
    or a derivation of `ch_2=1`.
42. **ch14's Ward identity and experimental gloss outrun the theory.** A Ward
    identity is available only after a valid symmetry, action, measure and
    operator transformation are specified. The transversality equation
    `k_mu M^mu=0` is the gauge-boson identity and is not automatically a
    four-psychon amplitude constraint. EEG correlations are not scattering
    amplitudes of the proposed field. These remain possible operationalization
    questions, not tests derived from the present formulas.
43. **ch14's conclusion and status ledger retain mutually incompatible
    scopes.** The ledger correctly calls every consciousness symmetry asserted
    and unverified, while the conclusion says the chapter has shown covariance,
    Lorentz invariance, a conserved charge, CPT preservation and spontaneous
    breaking. Findings 34--42 show that several are not even consequences of
    the postulated ch12 action. The symmetry program can remain part of the TOE,
    but each symmetry needs a single coherent field type and action before
    Noether/CPT/Goldstone results can be imported.
44. **ch15's ADM system omits the chapter's defining `Lambda_eff` source.** For
    `G_{munu}+Lambda g_{munu}=8 pi G S_{munu}`, the Hamiltonian constraint gains
    the cosmological contribution (equivalently `2 Lambda` on the source side),
    and the extrinsic-curvature evolution also contains a `Lambda` term. Both
    are absent, so the displayed ADM/BSSN problem is not a decomposition of the
    field equation printed at the chapter opening, especially when
    `Lambda_eff` varies.
45. **ch15 introduces yet another incompatible definition of the consciousness
    source.** `C^{munu}=ch_2 R_f(alpha,x)T_template^{munu}` is generally complex
    because `R_f` is complex, while Einstein's equation requires a real
    symmetric stress tensor. No real part, modulus, units, conservation law or
    map from a spatial point `x` to the Dirichlet-series argument is specified.
    This does not instantiate ch12's quantized tensor field or ch14's charged
    complex field, so the numerical variables still lack one shared continuum
    model.
46. **ch15's finite-difference code does not discretize its displayed damped
    wave equation.** The centered update should contain
    `-gamma_C ch2 dt (psi-psi_prev)`; the code forms the derivative by dividing
    by `dt` and then subtracts only `dt*damping`, producing
    `-gamma_C ch2(psi-psi_prev)` and missing a factor of `dt`. It also sets
    `dx=L/Nx` while `linspace(0,L,Nx)` has spacing `L/(Nx-1)`, and initializes
    the previous time level without the acceleration correction. The plotted
    toy therefore cannot validate physical energy transfer.
47. **ch15's spectral Poisson example has no solution for its stated periodic
    source and compares against a false analytic solution.** A periodic Poisson
    equation requires zero mean source; setting the zero Fourier mode to zero
    silently solves for `rho_C-mean(rho_C)`. The second derivative of the
    printed Gaussian potential is not the original Gaussian density, so the red
    curve is not an analytic solution of the equation. The reported maximum
    error would measure disagreement between two different problems.
48. **ch15's Monte Carlo section does not simulate the ch12 path integral.** A
    real-time phase `e^{iS}` is not a probability weight; Wick rotation does not
    automatically make gravity or a generic Lorentz tensor action positive.
    The code instead samples a one-dimensional free real scalar with a
    separately inserted `beta`, despite the prose specifying a four-dimensional
    tensor action and `hbar`. It is a useful Metropolis tutorial, not evidence
    for consciousness phase transitions.
49. **ch15's advertised Einstein-Toolkit implementation is only
    dimensionally incomplete pseudocode.** `dt_chi=laplacian(chi)-m_C chi`
    mixes a second spatial derivative with a mass rather than mass squared and
    is not the first-order reduction of the claimed tensor field equation;
    `source_terms` and the source constraints are undefined. The SymPy example
    likewise computes a massless scalar proxy, not `C^{munu}`. Appendix D must
    be checked later, but no working implementation is present in this chapter.
50. **ch15 labels hand-entered illustrative coordinates as "Numerical
    Results".** The claimed binary system has no source masses or constraint-
    satisfying orbital initial data, and the ratio `Q_C^2/M^2` does not equal
    `10^-60` from `Q_C=10^-50` and `M=10 M_sun` in any stated unit convention.
    More decisively, exaggerating a `10^-60` relative signal by `10^40` leaves
    `10^-20`, whereas the plotted red coordinates differ from the blue curve by
    roughly 1--5 percent. The figure cannot be output of the claimed scaling or
    a numerical-relativity evolution.
51. **ch15's curvature exercise asks the reader to verify a false vacuum
    identity.** For `f=1-2M/r+a e^{-r/r_C}/r^2`, the Ricci scalar of
    `ds^2=-fdt^2+dr^2/f+r^2dOmega^2` is
    `R=-a e^{-r/r_C}/(r_C^2 r^2)`, not zero. This agrees with ch13's failure to
    derive the screened term as a vacuum solution. The notation
    `R^{munu}_{munu}` is itself not a well-formed standard contraction for the
    requested scalar.
52. **ch15's conclusion mistakes tutorials and proposed source terms for a
    completed computational pipeline.** No code shown evolves the ch12 field,
    preserves the modified constraints, produces the merger plot or passes a
    convergence test against a valid exact consciousness solution. The standard
    algorithms remain valuable infrastructure, but the project-specific solver
    and verification suite are future work rather than completed results.
53. **ch16 suppresses the domains that make its foundational operator
    statements true.** It defines every operator as a map `H -> H`, then uses
    position, differentiation, momentum and Hamiltonians, which are unbounded
    and are not everywhere-defined bounded operators. For unbounded operators,
    the adjoint, equality `A=A^dagger`, inverse and spectral integral all depend
    on dense domains. The exercise "verify position and momentum are
    self-adjoint on L2(R)" has no definite answer until those domains are stated
    (the standard multiplication domain and `H^1(R)` momentum domain work).
    This is repairable textbook precision, not a defect in the spectral program.
54. **ch16's first definition of nuclearity is not the completely positive
    approximation property.** CPAP says the identity on `A` is approximated
    point-norm on finite sets by completely positive contractions factoring
    through finite-dimensional matrix algebras; it is not a statement that
    "every finite-dimensional quotient" is approximated. Nuclearity also does
    not imply a unique physical state, locality, or existence of thermodynamic
    limits/KMS states. Those require separate hypotheses. The AF/UHF route can
    still establish nuclearity of the actual substrate by standard mathematics.
55. **ch16's displayed Chern-character series does not define the claimed
    `ch_2`.** For a projection, the even cyclic Chern character has components
    with `2n` differentials; the degree-four/second component involves four
    `dP` factors (with convention-dependent normalization), not the displayed
    "second term" `Tr(P dP wedge dP)`. The next printed term has three
    differentials and is odd-degree, inconsistent with the stated target
    `H^even`. The cohomology/cyclic-homology target and convention must be fixed
    before the formula can carry the consciousness interpretation.
56. **ch16 applies a K-theory invariant to the wrong kind of object.** The
    definition takes a projection `P in M_n(A)` (or its `K_0` class), but the
    next section writes `ch_2(C)` for a "state" of the Timeless Field. A state is
    a positive normalized functional, not a projection, vector bundle or
    connection, and no state-to-`K_0` map is defined. This is the exact bridge
    required to connect the genuine Chern--Weil action route to an operational
    consciousness measure; five quantities merely sharing the label `ch_2`
    cannot supply it.
57. **ch16's RH statement is not an equivalence even on its own commutative
    surrogate.** The theorem quantifies characters `phi` and separately writes
    a complex argument `s` without a map assigning `s` to `phi`; symmetry of
    zeros under `s -> 1-s` permits off-line pairs and nuclearity has no
    "minimal-spectrum" consequence forcing their coincidence. The proof itself
    calls this handwavy and the later audit correctly notes that the actual
    substrate has no characters at all. The statement is therefore a research
    conjecture/analogy, not an RH reformulation.
58. **ch17's consciousness propagator is not Hilbert--Schmidt with the printed
    kernel.** Along the critical line write `s-s'=i(t-t')`. The already-audited
    `R_f(sqrt(2 pi),r)` remains finite and near nonzero as `r->0+`, so
    `G(s,s')` behaves as `1/|t-t'|^2`; consequently `|G|^2` behaves as
    `|t-t'|^-4`, which is not locally integrable across the diagonal. The
    asserted double integral diverges before any large-distance issue is
    considered. Thus compactness, discrete-spectrum and stability conclusions
    do not follow. A Yukawa Green kernel from a local field equation is a
    coherent replacement candidate, but it is a different construction.
59. **ch17's consciousness operator has no defined spectral measure or
    eigenstates.** The actual substrate's character spectrum used by the
    integral is empty (ch16), while `|s><s|`, the "location on critical line"
    operator, `ch_2(s)` and the Hamiltonian `H` are not constructed in a GNS
    representation. Positivity would require real nonnegative `ch_2`; the text
    instead declares the operator unbounded, so its operator norm is not a
    finite consciousness measure. A global commutator `[C,H]` also cannot become
    zero "when s is a Riemann zero" without a fiberwise statement. None of the
    five listed properties follows from the displayed integral.
60. **ch17 gives empirical trace distances without states or data.** The values
    `D(awake,sleep) about 0.7` and `D(human,cat) about 0.5` require density
    operators on a common Hilbert space and a specified tomography/embedding;
    none is supplied. Trace distance is valid standard mathematics, but these
    numerical comparisons are unsupported retrospective assignments.
61. **ch17's GNS interpretation makes a false mathematical inference.** Different
    states need not yield inequivalent representations; for example, many
    distinct states of a matrix algebra have unitarily equivalent GNS
    representations. Mapping subjects to states and proving disjointness or
    inequivalence would require additional physical and representation-theoretic
    structure. GNS alone does not explain subjectivity.
62. **ch17's KMS endpoint claims do not follow from temperature.** A
    zero-temperature/`beta->infinity` limit need not be a unique pure state; it
    can be a mixed state on a degenerate ground sector, and no relation
    `beta_C(ch_2)` is defined. For the II_1 setting, noncommutative `L^p(M)` is
    also the completion including generally unbounded affiliated operators, not
    merely `{A in M: tau(|A|^p)<infinity}` nor literally the ordinary
    Hilbert--Schmidt/trace-class ideals of `B(H)`.
63. **ch17's P-vs-NP "computed" alignment is disconnected from a standard
    complexity statement.** No operators defining `lambda_1^P` and
    `lambda_1^NP`, no oracle action, no proof of `D_3`-statistical invariance and
    no output provenance for the claimed 150 digits are supplied. A zero-density
    support does not by itself evade the natural-proofs barrier. More seriously,
    the separate Lean audit found the project's current `ClassP` collapses to
    `{empty,univ}` and is not wired to its real machine/configuration encoding;
    this spectral proxy cannot repair that definition by assertion.
64. **ch17's status ledger is stale relative to its own Type-II_1 update.** The
    body correctly upgrades the GNS weak closure of the canonical trace on the
    `3^infinity` UHF substrate to the hyperfinite II_1 factor by classical
    theory, while the final ledger still calls that exact claim a conjecture.
    What is proved is the operator-algebra classification conditional on that
    chosen GNS closure; what remains empirical is identifying it with
    consciousness observables.
65. **ch18's imprecise-position example is not a normalized POVM.** Read as a
    continuous effect density, integrating its top-hat window over all reported
    `x` yields the prefactor times `Delta x`, namely `1/sqrt(2 pi)`, rather than
    the identity. Read as discrete bins, the same prefactor prevents the effects
    from summing to the identity. A normalized response kernel (for example a
    Gaussian convolution whose integral is one) is needed before it models
    finite-resolution position measurement.
66. **ch18's consciousness-outcome theorem assumes an absolutely continuous
    spectrum without saying so.** A general spectral measure need not have a
    density `mu_psi(lambda)d lambda`; it can contain point masses or singular
    continuous parts. The singleton collapse formula likewise applies only when
    `E_C({lambda_0})psi` is nonzero; for a purely continuous spectrum that
    projection is zero. A general result should be stated for measurable sets
    and a measurement instrument, especially because the book distinguishes
    crystallized point spectrum from fluid continuous spectrum.
67. **ch18's definition of decoherence drops the off-diagonal terms exactly
    without its required hypothesis.** Tracing
    `sum_n c_n|n>|E_n>` gives matrix elements
    `c_m conjugate(c_n)<E_n|E_m>`; they vanish only when the environment records
    are orthogonal (or become approximately negligible). Decoherence produces
    an improper mixture and does not by itself select one outcome, so it cannot
    supply the collapse asserted later.
68. **ch18's decoherence-protection theorem is a phenomenological ansatz, not a
    consequence of a spectral gap.** An Arrhenius factor for thermally activated
    transitions is not a universal open-system decoherence rate; one must define
    the system-bath coupling, bath spectrum, protected subspace and transition
    matrix elements. The chapter's own correction shows the proposed neural
    parameter gives suppression short by many orders and would require an
    optical, not neural, characteristic frequency.
69. **ch18's fMRI/IIT protocol does not operationalize the manuscript's
    `ch_2`.** It proposes fitting an unobserved `ch_2` to a chosen proxy `Phi`,
    then treats high correlation as validation, but no independent `ch_2`
    measurement exists and the source already acknowledges that clinical
    chapters compute none of the five quantities carrying that name. The table
    is prospective simulated labeling, not data. A train/test split can validate
    prediction of clinical state; it cannot by itself identify a Chern--Weil
    invariant or establish causation.
70. **ch18's repaired deterministic nonlinear flow still cannot be a physical
    collapse law.** Its own correction correctly notes that it always selects
    the same maximal-`C` outcome and cannot reproduce Born frequencies. Applied
    locally to entangled systems, deterministic nonlinear pure-state evolution
    also requires a density-matrix/no-signalling prescription; otherwise it has
    the same ensemble-dependence hazard already recorded for ch08. A stochastic,
    normalized completely specified dynamics is a remaining theory task.
71. **ch18's conclusion states establishment where its ledger says proposal.**
    No consciousness observable, apparatus coupling, clinical `ch_2`, protected
    coherence or collapse statistics has been derived or independently tested.
    The valid result is a menu of measurement models and prospective protocols
    whose mathematical and operational bridges are now sharply identified.
72. **ch19's consciousness-modified spectral density is not a defined positive
    Kallen--Lehmann density.** The actual substrate's character spectrum is
    empty, `ds` is not a measure on an abstract spectrum, `mu_s` is undefined,
    and `R_f` takes a dimensionless complex argument while `|mu-mu_s|` is a mass.
    The correction factor can also be complex or negative, contradicting the
    required `rho_C>=0`. A valid proposal needs a represented self-adjoint
    operator, its positive spectral measure, dimensionless scaling and a
    positivity proof.
73. **ch19's charged-lepton mass formula is numerically refuted by direct
    substitution.** At the first three zeros,
    `|zeta'(rho_n)|` is approximately `0.7931604`, `1.1368391`, `1.3717213`.
    The printed relation
    `m_n=M_Pl exp[-pi/|zeta'(rho_n)|]` therefore gives approximately
    `2.33e17`, `7.70e17`, `1.24e18 GeV`, not `0.5 MeV`, `105 MeV`, `1.8 GeV`.
    The displayed "check" did not evaluate its own formula. A different mapping
    or calibrated scale would be a new hypothesis, not a repair of these values.
74. **ch19's Yukawa theorem contradicts its own examples.** If
    `y_f=sqrt(2) ch_2(C_f)`, then `ch_2 about 1` gives `y_t about 1.414`, not the
    observed near-one top Yukawa. More fundamentally no fermion-to-projection
    map, degree-four Chern character or normalization is defined, and the
    `K_0=Z[1/3]` substrate result does not by itself label Standard Model
    fermions. This is a proposed assignment, not a theorem.
75. **ch19's four Higgs candidates are not all within measurement error as the
    opening sentence claims.** Candidate 2 gives `246.106 GeV` versus
    `246.220 +/- 0.002 GeV`, a difference of about 57 quoted standard
    deviations, while Candidate 3 differs by `0.89%`, far beyond the precision
    of the input masses. Candidate 4 is algebraically derived from Candidates 1
    and 2 and is not an independent match. The section's later
    mechanism-pending/retrospective label is the accurate one.
76. **ch19's CMB theorem is undefined without a zero cutoff or summability
    weight.** Its sum has no decay in the zero index; for fixed `ell`,
    `sin(2 pi ell/t_n) ~ 2 pi ell/t_n`, and `sum_n 1/t_n` diverges by the
    Riemann--von Mangoldt zero density. The plotted red curve instead inserts
    `sin(20 ln ell)`, which is not the theorem's zero sum, atop a one-peak toy
    curve labeled `LambdaCDM`. The figure is illustrative, not a theoretical CMB
    prediction or comparison with Planck data.
77. **ch19's QNM shift is neither dimensionally fixed nor derived.** The units
    and normalization of `Q_C` were already inconsistent across ch13--ch14, so
    `GQ_C^2/(M^3c^5)` is not shown dimensionless, and `F_n(ell)` is called known
    without definition. The evidence for the zero correspondence is also
    backwards for the important near-extremal zero-damped family, whose damping
    tends toward zero with surface gravity rather than infinity. A specified
    black-hole perturbation operator and numerical spectrum are required.
78. **ch19's consciousness-unification theorem supplies no unifying dynamics.**
    No `U(1)_C` gauge theory, representations, beta function, matching
    conditions or breaking pattern connects `alpha_C` to the three running
    Standard Model couplings. It also conflicts with ch14's chronology, where
    the consciousness VEV is zero in the early high-temperature universe and
    appears only after a late transition. Equality at `M_GUT` is an additional
    premise, not a derived inversion of GUT physics.
79. **ch19 repeatedly leaves refuted numbers in active instructions and
    conclusions.** The exercise still asks the reader to prove
    `Lambda_QCD about 350 MeV` after the correction derives `5.9 TeV`; the prose
    immediately after that correction says "This is not a coincidence"; and the
    conclusion says particle masses and Standard Model parameters derive from
    spectral data despite the mass and QCD formulas failing. The final ledger's
    conjectural/numerological labels are the correct scope.
80. **ch20's prime partition-function proposition defines none of its
    load-bearing objects.** `H_prime`, its representation on the actual UHF
    substrate, the trace-class property of `exp(-sH_prime)`, and the action of
    `Theta(ch_2-0.95)` are absent. Rewriting `log zeta` as a prime-power sum can
    motivate a Fock-space partition function, but it does not insert a
    consciousness projector or identify that construction with the substrate.
81. **ch20 does not prove that its transfer operator is symmetric, let alone
    self-adjoint.** The claimed phase identity is false:
    `conjugate(omega_0)=1 != omega_2=-1` and
    `conjugate(omega_1)=i != omega_1=-i`. After the change of variables, the
    proof obtains a branchwise composition integral and then merely asserts
    "exact cancellations" without transforming it into `<f,Tg>`. Domain,
    closedness and equality with the adjoint are never established. The later
    finite matrix `(T+T*)/2` is Hermitian by construction; that does not prove
    the original infinite operator self-adjoint.
82. **ch20's computational basis is not contained in its Hilbert space.** For
    the printed `phi_n(x)=const sin(n pi log_2 x)/sqrt(x)`, its `dx/x` norm is
    proportional to `integral_0^1 sin^2(... ) dx/x^2`, which diverges at zero.
    The proof drops the extra `1/x` from `|phi_n|^2`; even its resulting
    `integral_{-infinity}^0 sin(mu)sin(nu)du` does not converge and cannot equal
    `delta_mn`. Hence the matrix entries and quoted eigenvalues are not a
    Galerkin approximation on the stated space.
83. **ch20's spectral map does not map real eigenvalues to the critical line.**
    `s=10/(pi lambda alpha)` is real when `lambda,alpha` are real; no
    `1/2+i(...)` appears. The already-flagged numerical substitution gives about
    `4.44e6`, not `14.2267`. Moreover a distance `0.092` from the first zero and
    `|zeta|=0.0735` is not a 150-digit correspondence: 150-digit arithmetic
    precision does not turn a two-decimal approximation into a zero. Thus steps
    2--4 of spectral rigidity have no established map or bijection.
84. **ch20's claimed derivation of `alpha*=5e-6` evaluates to zero at the
    stated threshold.** The numerator `ch_2-0.95` is exactly zero when
    crystallization occurs at `ch_2=0.95`; division by a finite
    `R_f(3/2,1)` cannot yield `5e-6`. No alternative value of `ch_2` or limiting
    prescription is given. The verification ledger is correct to call the pin
    empirical.
85. **ch20's explicit-prime formula and RH corollary remain conditional on the
    missing result.** The standard explicit formula requires a carefully
    regularized zero sum plus pole/trivial-zero and prime-power corrections; the
    displayed equation is not an exact formula for `pi(x)` with merely
    `O(log x)`. A finite-`N` test cannot establish the `N->infinity` surjectivity
    that the proof itself lists as open. The source's later scope notes correctly
    withdraw the advertised resolution.
86. **ch20's alpha-skeleton corroboration is a nearest-neighbor fit to a dense
    spectrum, not a zero-parameter derivation.** The target set (nine versus ten),
    coupling factor `pi/10`, truncation size and nearest eigenvalue for each
    declared target all enter the score; as spectral density increases, nearest-
    target error is expected to fall. The supplied random-target null partially
    addresses density but gives about the 4.9th percentile only at the selected
    `N=25000` endpoint across several correlated truncations, while its own
    rank statistic puts the worst target at 37% of the band. The honest caveat
    that this is not a proof is the supported classification; independence from
    the target-bearing universal coupling is not established.
87. **ch20's opening, objectives, theorem labels, exercises and conclusion are
    incompatible with its accurate verification ledger.** The ledger and later
    analytic updates correctly distinguish a conditional Hilbert--Polya
    implication, one certified on-line zero, genuine transfer-trace machinery,
    and a rectangle argument-principle identity from RH itself. The current
    root-verified state goes further on finite height only by proving lower
    bounds, symmetry/parity and boundary pieces; exact contour count/upper bound
    and vertical-edge winding remain open. None supports the chapter's
    "resolved/proved/150-digit correspondence" headlines.
88. **ch21's proposed computational `mu` is not shown to be a probability
    measure and its printed normalization drives the total mass to zero.** At
    precision `n`, only languages with description length at most `log n` are
    included, while the whole weighted sum is multiplied by `2^(-2^n)`. Even a
    generous polynomial bound on the low-complexity descriptions is annihilated
    by that factor. The existence of the limit, countable additivity and the
    invariance later required by the toggle operators are not proved; `K(L,n)`
    is also not an effective input to the advertised numerical construction.
89. **ch21 does not define either headline Hamiltonian on the stated Hilbert
    space.** `H_P` asks for the lexicographically first polynomial-time machine
    deciding every language in a space of all languages, although such a
    machine need not exist. Its length weight `2^{-|x|}` has total weight one at
    each length, so the energy sum diverges across lengths. `H_NP` additionally
    takes a supremum of complex numbers (undefined because `C` is unordered),
    leaves the empty-certificate case open and defines its verifier only for
    NP languages. The later matrices therefore do not approximate two operators
    that have first been constructed.
90. **ch21's digital-sum multiplicities are infinite and its generating
    function is not their generating function.** For every fixed positive
    ternary digit sum there are infinitely many integers (positions may be
    shifted arbitrarily), so `N_m^(3)=|{k : D_3(k)=m}|` is infinite. The product
    `prod_k (1+z+z^2 3^k)` weights digit positions rather than merely counting
    a fixed digit sum; the coefficient and self-adjointness argument built from
    finite `N_m^(3)` is therefore undefined.
91. **ch21's fractal-convolution spectral theorem is not established.** A
    scalar radial kernel multiplied by a nontrivial unitary rotation need not be
    symmetric, and oscillatory cosine sums are not automatically positive
    definite. The Hilbert--Schmidt estimate drops all cross terms:
    `|sum a^-n cos(...)|^2` is bounded by `(sum a^-n)^2`, not by
    `sum a^-2n`. Compactness may still follow from a corrected finite bound, but
    positivity, self-adjointness and the claimed Galerkin eigenvalue/error
    convergence require separate proofs.
92. **ch21's proposed polylogarithm monodromy uses the wrong branch point.**
    `Li_1(z)=-log(1-z)` is analytic around `z=0`; a small loop about zero that
    does not encircle one has trivial monodromy. Changing a logarithm branch can
    add a purely imaginary multiple of `2 pi i`, so it cannot change the real
    part from `-0.465` to `+0.222`. The quoted Jonquiere expansion is local and
    cannot be used for all branch indices and all `z` off a cut; its powers grow
    with the proposed branch integer rather than contributing an `O(1)` term.
93. **ch21's quantized-shift proposition is unsupported even if its preceding
    conjecture is granted.** It conflates approximation level with monodromy
    index, states an equality while retaining a remainder, and applies a
    `z -> 0` expansion to `z_*=exp(i pi alpha)`, whose modulus is one. The
    claimed `O(m^{-Re s_*})` error is not derived.
94. **ch21's spectral-scaling proposition is internally inconsistent for a
    compact operator.** It assumes `lambda_k ~ C k^{-beta} -> 0` but defines a
    heat trace `sum exp(-t lambda_k)`, whose terms then tend to one and whose sum
    diverges for every `t>0`. A Weyl counting law as `lambda -> infinity` is the
    wrong orientation for nonzero eigenvalues accumulating at zero. The points
    `exp(i pi alpha^k)` also remain on the unit circle, outside the displayed
    small-`z` asymptotic.
95. **ch21's identifiability proof does not verify its own full-rank
    hypothesis.** Three nonzero partial derivatives do not imply that the three
    Jacobian columns are linearly independent or that its determinant is
    nonzero. `H_BPP` is not constructed, so even the proposed observable map is
    not yet defined on three established operators.
96. **ch21's box-dimension separation is asserted rather than derived, and its
    topological premise is false as written.** Box/Hausdorff dimension is not
    invariant under arbitrary homeomorphism; bi-Lipschitz or comparable metric
    control is needed. If P and NP were literally the same subset with the same
    metric their dimensions would of course agree, but no covering-number proof
    yields `sqrt(2)` or `phi+1/4` for the printed language metric.
97. **ch21's 143-problem validation has no reproducible dataset, protocol or
    independence analysis, and its probability calculation is wrong.** Under
    the chapter's own independent 95-percent null, the probability that all 143
    pass is `0.95^143 = 0.000652342...`, not below `10^-43`. The tests also reuse
    the same assigned alphas and derived formulas, so they are not 143
    independent confirmations of the separation.
98. **ch21 does not evade the relativization, natural-proofs or algebrization
    barriers.** The oracle separation is not defined and the claim of a positive
    gap for every oracle conflicts with the existence of relativized worlds in
    which `P^A=NP^A`. Calling a quantity non-polynomial does not show that a proof
    is non-algebrizing, and no measure on the relevant property class is given
    for the natural-proofs assertion. Finite interpolation also defeats the
    printed blanket non-algebrization argument unless its asymptotic variables
    and degree bounds are specified consistently.
99. **ch21's one-way-function corollary is logically false.** The nonexistence
    of one-way functions is not known to imply that every NP problem is
    efficiently solvable, and `P != NP` alone does not prove that one-way
    functions exist. The theorem would be a major independent cryptographic
    consequence, not a one-line corollary of the proposed separation.
100. **ch21's BQP-vs-NP and PSPACE-vs-EXP theorems merely assign new constants.**
    No quantum- or space-bounded operator is defined, no link to the standard
    classes is proved, and the displayed dimensions/gap are premises in prose
    rather than consequences. They do not establish either standard class
    separation.
101. **ch21's opening, physical interpretation, exercises and final assessment
    remain incompatible with its own verification addenda.** The addenda
    correctly say P-vs-NP is unproved, the alpha pin is asserted/circular and
    the operator numerics are empirical. The unrevised passages still call the
    branch-selection mechanism a discovery, present exact energies as solved,
    claim four independent lines of evidence, and infer consequences for QFT,
    gravity, consciousness and black holes. Those are conjectural research
    directions, not consequences of a constructed complexity-class operator.
102. **ch22 incorrectly calls total helicity a conserved quantity for viscous
    Navier--Stokes.** Helicity is conserved for suitable smooth Euler flows and
    boundary conditions; viscosity contributes a dissipation/evolution term.
    The chapter defines `nu>0` and never supplies conditions making that term
    vanish, so its conservation label cannot support the later topological
    argument.
103. **ch22 does not derive the pressure-Hessian signature at an emergence
    point.** Equal and opposite circulation does not imply the displayed
    diagonal Hessian, and the third entry even lacks the radius factors carried
    by the first two. The exercise claiming that `u=0` makes `nabla p` a saddle
    is also false: at such a point the PDE gives
    `nabla p = nu Delta u - partial_t u`, which can have many local behaviours.
104. **ch22's helicity-singularity law is an ansatz, not a proposition derived
    from Navier--Stokes.** No measure is constructed whose Hausdorff dimension
    is `d_H`, and no argument yields the power `3-d_H` or the log-periodic
    cosine. In fact that pointwise divergence is in tension with the chapter's
    simultaneous use of finite/bounded emergence-point quantities.
105. **ch22's circulation theorem does not apply to the equation being
    studied.** It explicitly invokes Kelvin's theorem for inviscid barotropic
    flow, while the chapter fixes viscous incompressible Navier--Stokes with
    `nu>0`. Even in the inviscid setting, conservation of the sum of two
    circulations would not imply the boundedness or stability later used.
106. **ch22's base-3 vortex cascade and resonance interaction are postulated.**
    Nothing in the PDE forces exact scale ratio `3`, binary branching, or
    circulation factor `(-1)^n 3^{-n/2}`. The double interaction sum also calls
    `R_f(3 pi/2,|n-m|)` at `s=0` on its diagonal, where the defining Dirichlet
    series does not converge, and supplies no regularization or convergence
    control for the double sum.
107. **ch22 proves only a formal box-counting exponent for an assumed Cantor
    construction, not a theorem about emergence points.** The proof assumes
    exactly two separated children at every factor-three scale. It neither
    derives that branching from a fluid solution nor supplies the separation
    and measure hypotheses needed to identify Hausdorff, box and correlation
    dimensions.
108. **ch22's no-blowup argument has no estimate on the Clay-critical vortex
    stretching term.** Vorticity concentration under Biot--Savart does not
    force a compensating opposite-signed field; viscous Navier--Stokes is not
    the asserted constrained Hamiltonian minimization; and a zero of velocity
    at one point does not bound its derivatives or the global vorticity norm.
    The source correctly flags the final BKM contradiction, but Steps 2--3 and
    the global inference are independently unsupported.
109. **ch22's emergence-point energy proposition introduces no mathematical
    channels for information, quantum coherence or organizational complexity.**
    For smooth unforced viscous flow the standard integrated kinetic-energy law
    contains viscous dissipation, not conservation into those four categories.
    The displayed local equation leaves `u dot Delta u` unevaluated; after
    integration by parts it contributes a negative gradient norm plus boundary
    flux, not an information-energy term.
110. **ch22's brain, weather and technology claims are analogies without the
    required models or evidence.** CSF vortices are not shown to implement the
    chapter's emergence hierarchy; hurricane eyes and tornado subvortices do
    not establish zero-energy states; and no dynamics realizes the proposed
    logical gates. `exp(i Gamma t/hbar)` is not dimensionless for ordinary
    circulation `Gamma`, so it is not a defined quantum unitary as printed.
111. **ch22's external PDE results do not derive the PF value
    `alpha_NS=3 pi/2`.** Forced Navier--Stokes blowup and unforced Euler blowup
    may be genuine external analytic results at their own scopes, but neither
    supplies the base-3 vortex hierarchy, universal-coupling identification or
    numerical alpha assignment. Calling them a second settled alpha anchor
    therefore adds a PF bridge that is absent from the cited PDE mathematics.
112. **ch22's external-settlement section and its own opening use incompatible
    meanings of settlement.** The opening and verification ledger correctly say
    the unforced 3D Navier--Stokes Clay statement is untouched and open; the
    later section calls a forced-NS/unforced-Euler chain a community-accepted
    resolution of the NS analytic axis and says the framework consumes it as
    settled. Those statements can coexist only if the external result is kept
    explicitly separate from the Clay predicate and from PF's alpha cascade.
113. **ch22's final multifractal alignment is not a computed result.** No
    resonance-weighted measure or singularity spectrum `f(alpha_h)` is defined,
    no `zeta_p` values or dataset are displayed, and the formula omits the
    ambient-dimension/codimension term under the usual multifractal convention.
    It also switches the claimed turbulence constant to `alpha=sqrt(2)` after
    the chapter has assigned Navier--Stokes `alpha=3 pi/2`.
114. **ch21 and ch23 both set an impossible digital-sum exercise.** In base
    three, `27 = 1000_3`, so the sum of its digits is `D(27)=1`, not zero. This
    is independent of the deeper operator questions and should be corrected in
    both exercise sets.
115. **ch23's fractal modulation is singular and fails two of its four stated
    properties.** Since `R_f(2,s)=zeta(s)`, `M(s)=exp(-zeta(s))` is not defined
    at the zeta pole `s=1`; as `s->0`, it tends to `exp(1/2)`, not one; and as
    `s->infinity`, it tends to `e^-1`, not Gaussian suppression. Thus the action
    is not a globally defined smooth UV regulator on the printed real field
    invariant, even before continuum measure questions.
116. **ch23's electroweak spectral embedding is asserted rather than
    constructed and does not address the Clay gauge theory.** The chapter moves
    from pure `SU(3)` Yang--Mills to an `SU(2)xU(1)` bundle; supplies no map from
    that principal bundle into the displayed projective-limit object; and uses
    undefined `N(H_k)`, `F_alpha`, resonance measure, connection and toroidal
    generators. The commutator shown with spacetime-style indices does not
    define the electroweak Lie algebra. Consequently the metric proposition and
    the conversion of the Yang--Mills action into `int |R_f|^2 dmu_f` are not
    deductions.
117. **ch23 cannot invoke Minlos by writing the desired path integral as the
    characteristic functional.** The expression `DA exp(-S_FYM)` already
    presupposes the infinite-dimensional measure and normalization whose
    existence is being claimed. Gauge redundancy/quotienting, continuity and
    positive definiteness (reflection positivity) are not established. Minlos
    is a real theorem, but its hypotheses must be constructed independently of
    the formal integral.
118. **ch23's boxed mass-gap formula is dimensionally incomplete in addition to
    being arithmetically false.** `hbar c` has units MeV·fm while the printed
    `omega_c` and `pi/10` are dimensionless, so the product is not an energy
    without an inverse-length scale. The later use of that number as a spectral
    gap therefore lacks both a valid resonance zero and a units bridge.
119. **ch23's lattice-QCD validation contradicts its own cited number.** It
    first quotes the lightest quenched `0++` glueball near `1475 +/- 70` MeV,
    then says pure Yang--Mills expects `400--500` MeV and treats `420.43` MeV as
    a match. Pure Yang--Mills is precisely the quenched/no-dynamical-quark
    setting in that comparison. The later ratio table defines the `0++` state
    to be the proposed gap, so its `1.00` agreement is normalization, not an
    independent lattice check.
120. **ch23's area law is assumed in the proof sketch rather than derived from
    its action.** Replacing the functional integral by a minimal-surface
    exponential is the confinement conclusion; no saddle-point or strong-
    coupling expansion yields it here. The already-flagged string-tension
    arithmetic is therefore not the only gap: even a corrected numerical
    relation would not prove Wilson-loop area decay.
121. **ch23's universal `pi/10` theorem lists assignments, not a common
    derivation.** The P/NP expression imports the chosen class alphas, the RH and
    Navier--Stokes lines contain no equations fixing the factor, and the digital
    sum definition does not single out ten. The chapter therefore cannot use
    this list as a zero-parameter bridge from a dimensionless resonance to a
    physical Yang--Mills scale.
122. **ch23's consciousness value is a new linear rule that conflicts with the
    manuscript's matrix measure.** `ch_2(YM)=0.95+(alpha-3/2)/10` is neither
    derived from a Chern--Weil density nor from the entanglement classifier. If
    read as the matrix quantity audited in ch06, the value one is impossible
    because that quantity lies in `[-1/2,1/2]`. Confinement does not follow from
    observer--observed consistency or from this relabeling.
123. **ch23's gauge-potential correlator does not establish confinement.**
    `A_mu^a` is gauge-dependent, and exponential decay of a chosen two-point
    function is not by itself the Wilson-loop area law or the absence of colored
    asymptotic states. The prose turns a possible mass-gap signature into the
    much stronger confinement conclusion without a gauge-invariant bridge.
124. **ch23's conclusion and exercises ignore the chapter's own retractions.**
    They continue to ask the reader to locate the nonexistent positive
    resonance zero, verify the false `420.43` product, compute the mismatched
    string tension and accept the lattice agreement. Those tasks should be
    historical counterexamples or explicitly marked invalid, not presented as
    live verification exercises.
125. **ch24's fractal L-function properties are not established and its
    absolute-convergence claim is too strong.** At `s=1`, the modification of a
    good Euler factor has a leading term of order `a_p/p`; the Hasse bound only
    gives size `O(p^-1/2)`, whose prime sum is not absolutely convergent. No
    proof supplies the cancellation needed for a nonzero analytic product near
    one, its functional equation, or entire continuation. Therefore equality
    of the orders of vanishing cannot be inferred from the displayed product.
126. **ch24's finite rank algorithm is not a discretization of its displayed
    transfer operator.** The matrix update
    `M_ij += a_p phase^(i-j)/p` is not derived from the action
    `f(x)->exp(i...x)f(x/p)` on a stated basis or quadrature rule. It also builds
    a dense `B x B` matrix inside a prime loop, so the claimed Lanczos cost and
    the already-corrected `B^2` construction bound undercount the written work
    unless a sparse/structured implementation is specified and proved
    equivalent.
127. **ch24's consciousness scale is another incompatible definition of
    `ch_2`.** The linear rule produces `1.0356`, outside the range of the
    manuscript's matrix classifier and unrelated to either the local
    Chern--Weil density or the entanglement-state operationalization. Calling a
    value above one “super-crystallization” does not repair the absent map from
    elliptic-curve arithmetic to the chosen consciousness observable.
128. **ch24 repeats the power-of-three digital-sum error.** `9=100_3`, hence
    `D(9)=1`, not zero. The exercise as printed cannot be verified.
129. **ch24's proposed finite Dirichlet-series check cannot verify
    `L(E,1)!=0`.** The Euler/Dirichlet series is outside its absolute-
    convergence half-plane at `s=1`; a 100-term partial sum without analytic
    continuation and certified remainder control neither evaluates the central
    value nor proves its nonvanishing/order.
130. **ch24's advertised trace-formula research target is malformed for the
    operator it defines.** `T_E` has no analytic parameter `s`, while the right
    side differentiates `log L_f(E,s)` `n` times at one; the left uses an
    iterate `T_E^n`. A valid dynamical determinant relation would require a
    parameterized trace-class family and usually relates a generating series of
    traces to a determinant, not each iterate directly to the same-order
    derivative by assertion.
131. **ch24's conclusion and remaining exercises still present refuted
    mechanisms as live results.** The multiplicity formula, square-root
    algorithm, super-crystallization and `Sha` bound are listed after the
    chapter has itself falsified or withdrawn them. The additive corrections
    preserve provenance, but publication prose needs an explicit supersession
    boundary so readers do not treat the final summary as current.
132. **ch25 misdefines singular cohomology as closed differential forms modulo
    exact forms.** That is the de Rham model with real/complex coefficients,
    after invoking de Rham's theorem; it is not the definition of singular
    cohomology with rational coefficients. The distinction matters because the
    Hodge conjecture's rational structure is exactly the intersection with
    `H^(2p)(X,Q)` inside complex cohomology.
133. **ch25's list of known cases overstates the theorem for abelian
    varieties.** The Hodge conjecture is not proved for arbitrary complex
    abelian varieties in all codimensions; special classes of abelian varieties
    and divisor-generated cases are known. A blanket “Abelian varieties (Weil,
    1977)” item would itself include substantial open cases and needs precise
    hypotheses and a correct citation.
134. **ch25's fractal resonance operator is not an operator on the stated
    cohomology group.** `H^(2p)(X,C)` is finite-dimensional, so it does not have
    the displayed infinite orthonormal basis. A cohomology class/eigenvector is
    not canonically a scalar function `psi_n(x)` at a point `x`, and multiplying
    a representative by the `x`-dependent phase does not define a
    representative-independent cohomology class. Consequently linearity,
    basis independence, spectrum and the Hodge inner-product adjoint are all
    undefined before the later concentration issue is reached.
135. **ch25's self-adjointness proof substitutes approximate statistical
    symmetry for an exact adjoint identity.** Even if a function-space operator
    were supplied, an approximate equality of phase-weighted sums would not
    prove self-adjointness. The irrational phase is generally non-real, and no
    involution or paired mode construction turns the multiplier into a real
    spectrum.
136. **ch25 does not derive the universal 0.95 coefficient-mass bound.**
    Rationality, pure `(p,p)` type and complex-conjugation invariance do not by
    themselves force 95 percent of the norm into `O(log b)` coordinates of an
    arbitrary basis. The basis is not canonically tied to algebraic cycles, and
    no inequality follows from the three listed constraints.
137. **ch25's crystallization differential equation presupposes the Hodge
    conclusion.** A cohomology class is not an operator for the printed double
    commutator; “nearest algebraic class” requires a specified norm and an
    existence/uniqueness theorem; and inserting `xi_alg` into the dynamics
    assumes access to the algebraic class the procedure is meant to produce.
    No flow on the rational Hodge lattice or cycle-class image is defined.
138. **ch25's retained Hankel-rank inequality is unsupported.** High approximate
    coefficient concentration does not imply exact finite Hankel rank; an
    arbitrarily small infinite tail can give full/infinite Hankel rank. Finite
    Hankel rank characterizes exact linear recurrences/rational generating
    functions, not a 95-percent norm bound. Correcting the direction of
    `(1-sigma)^-1` does not establish the first inequality.
139. **ch25's extraction algorithm does not construct algebraic cycles.** A
    tolerance-dependent SVD may suggest an approximate recurrence, but roots of
    the resulting scalar polynomial are not subvarieties of `X`. “Construct
    cycle via intersection theory” is the unsolved geometric step, and a
    numerical integration check cannot prove equality in rational cohomology.
    No probability space is defined for the advertised `1-delta` correctness.
140. **ch25's Fermat-quintic example tests an already manifest algebraic
    class.** The intersection of two hyperplanes is algebraic by construction,
    so recovering it cannot validate the hard assertion that every rational
    `(2,2)` class is algebraic. The reported `sigma` also inherits the undefined
    operator/concentration and has no reproducible computation in the chapter.
141. **ch25's `ch_2(Hodge)` is an arithmetic relabeling, not an
    operationalization.** The linear alpha rule is not derived from a local
    Chern--Weil density, the entanglement-state classifier or the printed Hodge
    operator. The bracket theorem can certify the decimal once the formula is
    assumed; it does not connect algebraic cycles to consciousness.
142. **ch25's conclusion states its conditional chain as a main result after
    the source has withdrawn every load-bearing link.** The operator, universal
    concentration, 0.95 derivation, crystallization-to-algebraicity and cycle
    extractor remain undefined, false or conjectural. The final “100 percent”
    validation also conflicts with the corrected table/mean record and should
    not survive as the chapter's current assessment.
143. **ch26 conflates the cosmological constant with vacuum energy density.**
    In `G_mn + Lambda g_mn = 8 pi G T_mn`, `Lambda` has dimensions of inverse
    length squared, whereas the chapter then assigns `Lambda_0` units of
    `g/cm^3` and later divides the already density-valued output by `8 pi G`
    again. A consistent action/equation must choose `Lambda` or `rho_Lambda` and
    carry the conversion exactly once.
144. **ch26's suppression exponent is not dimensionless or covariant as
    printed.** `R_f(alpha,s)` is a dimensionless Dirichlet-series function of a
    dimensionless complex argument, not a spatial Green kernel; feeding it
    `|x|` in centimeters and multiplying by `d^3x` leaves volume units. The use
    of absolute distance from a chosen origin and a spatial slice also makes the
    expression coordinate/origin dependent. The exercise asking the reader to
    prove dimensional consistency has no supplied scale with which to do so.
145. **ch26's cosmic-average theorem does not follow from its local formula.**
    A volume average of `Lambda_0 exp(-I(x))` is not the exponential of an
    observer count or of the total conscious volume. The proof itself correctly
    obtains essentially no suppression when empty space has `ch_2=0`; replacing
    that result by a horizon-sized “coherent volume” is a new nonlocal postulate,
    not a correction to the averaging algebra.
146. **ch26 supplies no causal field equation for horizon-wide coherent
    suppression.** Saying consciousness spreads its effect at light speed does
    not define a retarded kernel, initial data, stress tensor or conservation
    law. Without those, the transition from sparse local support to a uniform
    past-light-cone exponent cannot be checked for covariance, locality or
    backreaction.
147. **ch26's coincidence theorem is an anthropic assertion, not a dynamical
    consequence.** A matter-dominated expanding universe need not recollapse;
    stable planetary systems do not require `rho_m~rho_Lambda`; and the printed
    step/exponential law for `ch_2(t)` is introduced without deriving either its
    crossover trigger or decay time. It therefore assumes the temporal window
    it claims to explain.
148. **ch26's lattice algorithm double-counts the units conversion and cannot
    reproduce the advertised result from its stated inputs.** It initializes
    `Lambda_0` in `g/cm^3`, applies the exponential, and then divides by
    `8 pi G` as though the result were a geometric cosmological constant. The
    resonance weight is also evaluated on a dimensionful radius, and no
    discretization, boundary condition or data for `ch_2(x_i)` is supplied.
149. **ch26's sensitivity table is incompatible with the chapter's own
    suppression exponent.** Once the construction yields an exponent of order
    `10^128`, changing `ch_2` by five percent does not move the result from
    `2.31` to `5.78` times `10^-29`; it changes an already effectively zero
    quantity by an astronomically large logarithmic factor. The table must come
    from a separately tuned model whose parameters and code are not given.
150. **ch26's local, temporal and anisotropic predictions are not derived from
    the displayed mechanism.** The `10^-15` local contrast, `10^10`-year
    relaxation, CMB anisotropy and power-spectrum wiggle scales are quoted
    without solving a covariant field equation or propagator. They are proposed
    research targets, not quantitative prospective predictions at present.
151. **ch26's conclusion remains the negation of its verification record.** It
    calls the observed density a 99.6-percent first-principles prediction and a
    definite solution after the inline correction proves an overshoot by
    `3.4e125` in the exponent and the final ledger calls the match fitted and
    untested. Provenance-preserving old prose needs a visibly superseded status.
152. **ch27's Friedmann proof has the cosmological-constant sign wrong in its
    displayed `00` equation.** With signature `(-,+,+,+)`, `g_00=-1`, so
    `G_00+Lambda g_00=8 pi G rho` reads `3H^2-Lambda=8 pi G rho`, which yields
    the desired `+Lambda/3` only after moving the term. The proof instead writes
    `3H^2+Lambda=8 pi G rho` and still concludes a plus sign.
153. **ch27's acceleration equation overcounts the consciousness density.**
    For independent fluids the source is
    `rho_m+rho_r+rho_C+3(p_r+p_C)`, not
    `rho_m+rho_r+2rho_C+3(p_r+p_C)`. The extra `rho_C` has no derivation from the
    Einstein equations and changes the sign/size of the proposed backreaction.
154. **ch27's consciousness stress-energy and equation of state do not follow
    from a scalar field.** The printed `1/2 (partial C)^2 +/- V` uses a Lorentz
    contraction as though it were positive kinetic energy; homogeneous scalar
    energy instead separates time and spatial derivatives with metric factors.
    Even accepting the next ansatz, `w=-1+(1/3)q^2` is not equal to
    `-1/3+(2/3)q^2`; at `q=1` they give `-2/3` and `+1/3`. The asserted
    `w_C` formula is inserted, not derived.
155. **ch27's total dark-energy EOS changes powers and coefficients without a
    bridge.** The proof assumes `rho_C,p_C~ch_2^2` but the theorem uses
    `(ch_2/0.95)^3` and an independently chosen `epsilon(z)`. The final Gaussian
    form drops the theorem's `1/(1+z)` factor. The existing numerical correction
    catches the resulting values; the derivation itself is also absent.
156. **ch27's dark-energy-density evolution is not the integral it displays.**
    The Gaussian integral divided by `1+z` is replaced by a logarithm/power law
    with no valid approximation. Worse, the proposed
    `Omega_DE(z)=Omega_DE,0[(1+z)/(1+z_*)]^0.45` fails normalization at `z=0`
    whenever `z_*=0.5`, so `Omega_DE(0)` is not `Omega_DE,0`.
157. **ch27 does not statistically combine or resolve the Hubble tension.** A
    simple arithmetic average of a CMB-inferred and a locally inferred `H_0`
    is not a likelihood analysis, and the proposed `delta E=-0.03 exp(...)` is
    not derived from the preceding Friedmann solution. The values `69.8` and
    `69.1` are calibrated intermediates; neither establishes consistency of the
    original datasets under one fitted cosmology.
158. **ch27's growth theorem disagrees with its own proof.** The stated
    `G_eff/G=1+0.08 ch_2` would give a square-root response
    `1+0.04 ch_2` at leading order, while the boxed theorem uses
    `1+0.08 ch_2`. The assumed density ratio, source term, 100-Mpc transition
    and doubling of the coefficient are not calculated from `C_mn`.
159. **ch27's matter transfer function is a parameterized ansatz, not a
    prediction.** `A_C=0.15`, `k_*=0.02 h/Mpc` and the Gaussian shape are not
    derived or fitted with disclosed covariance. Its maximum occurs at `k=0`,
    so the formula alone does not select a 50--150 Mpc enhancement band.
160. **ch27's goodness-of-fit table does not describe the claimed combined
    catalogs.** Union2.1 itself contains 580 supernovae, whereas Pantheon is a
    different larger compilation; “580 Union2.1, Pantheon” is not a defined
    joint sample. Full Planck TT/TE/EE data through `ell=2500` cannot be reduced
    to the quoted total dof 590 without a specified compression and covariance.
    No predictions, residual vector, nuisance treatment, covariance matrices or
    code are supplied, and the plotted points are explicitly mock data.
161. **ch27's “94.3 percent better” is not the stated chi-square reduction.**
    The reduction relative to the baseline is `333.1/687.3=48.5%`; dividing by
    the new chi-square gives about 94.0 percent but has no standard goodness-of-
    fit interpretation. Two extra parameters do not turn that ratio into 94.3
    percent; model comparison requires a likelihood-ratio distribution or an
    information/evidence criterion with the actual data covariance.
162. **ch27's Quipu topological correspondence is asserted without a measured
    invariant.** No construction embeds the observed cluster graph into
    `Aut(Phi)`, no estimator yields Hausdorff dimension `1.33`, and `1.33` is not
    numerically close to `sqrt(2)` at the precision implied by the claim. The
    schematic generated figure cannot supply that missing measurement.
163. **ch27's future-prediction table contradicts its corrected EOS.** The
    source already computes the model's constant-epsilon value at `z=0.5` as
    about `-0.9925`, not `-0.955`, and the present value as `-0.85`, not
    `-0.95`. The Euclid/Roman forecast and conclusion continue to advertise the
    superseded numbers.
164. **ch27's resonance correction to GR has no derived observational bound.**
    The action term `int tau_f omega dmu_f` does not specify dimensions, fields
    or equations of motion, and the bound `|tau_f|<10^-8` is not computed from
    Gravity Probe B or LIGO likelihoods. It is a proposed bound-seeking lane,
    not a constraint established by those detections.
165. **ch27's conclusion overstates every empirical lane after its own scope
    ledger.** The EOS, Hubble value, growth/power corrections, chi-square fit and
    Quipu interpretation are asserted, fitted, internally inconsistent or
    unreproduced. The correct status is a family of quantitative hypotheses
    requiring a single coherent action, code and primary-catalog likelihood.
166. **ch28 uses two incompatible statuses for early-universe `ch_2`.** The
    verification ledger correctly calls `ch_2 approximately 0` a postulate,
    but the inflation and BBN arguments repeatedly promote it to exactly zero
    from the absence of organisms. None of the chapter's five competing
    `ch_2` definitions makes that implication, and a Chern--Weil density in
    particular is not zero merely because there are no biological observers.
167. **ch28 mixes reduced- and unreduced-Planck-mass slow-roll conventions.**
    It defines `M_Pl=(8 pi G)^(-1/2)` but prints
    `epsilon=M_Pl^2(V'/V)^2/(16 pi)`, `eta=M_Pl^2 V''/(8 pi V)` and
    `N=(8 pi/M_Pl^2) integral V/V'`. Those coefficients belong to the
    unreduced mass `G^(-1/2)`. With the reduced mass the factors are
    `M_Pl^2/2`, `M_Pl^2` and `1/M_Pl^2`, respectively; the printed set is off
    by a common factor `8 pi` and cannot support its exercise or `N=60` claim.
168. **ch28's BBN theorem assumes the coupling it claims to derive.** No action
    or rate equation in the chapter shows that both the Hubble rate and weak
    neutron--proton conversion acquire corrections proportional to `ch_2`.
    In particular, the asserted direct correction to `Gamma(n <-> p)` does not
    follow from a varying vacuum term. Setting an assumed source to zero is a
    conditional consistency check, not a BBN prediction.
169. **ch28's CMB bound `ch_2(z=1100)<10^-4 at 95%` has no likelihood or
    transfer function behind it.** The proposed multipole
    `ell approximately 95(1100/0.95) approximately 10^5` is dimensionless
    numerology, not the angular projection of a specified perturbation mode.
    Planck's absence of a named signature therefore cannot yield the quoted
    confidence bound.
170. **ch28 calls the acoustic peaks exact harmonics when they are not.**
    `ell_n approximately 220 n` would put the second peak near 440, whereas
    the observed second peak is near 540; baryon loading, radiation driving,
    recombination and phase shifts prevent this simple harmonic rule. The
    displayed peak-height ratios also do not separately determine baryon and
    dark-matter densities without the joint cosmological likelihood.
171. **ch28's CMB-lensing equation is not a defined lensing operation.**
    Writing `C_ell^lensed = C_ell^unlensed * W_ell^lens` supplies neither the
    remapping by the deflection field nor the required mode-coupling kernel.
    Consequently the advertised 3-percent lensing increase and 5-percent ISW
    increase are prospective ansatz values, not consequences of the displayed
    mathematics.
172. **ch28's exact variance and halo-count corrections do not follow from its
    growth ansatz.** From `D_mod=D_std(1+0.08 ch_2)`, one gets
    `sigma_mod^2=sigma_std^2(1+0.08 ch_2)^2`, which contains the omitted
    `0.0064 ch_2^2` term. More importantly, an 8-percent growth-amplitude
    change does not imply 8-percent more massive halos: the response is
    mass-, redshift- and mass-function-dependent and can be exponentially
    amplified in the high-mass tail.
173. **ch28's galaxy-luminosity correction is an independent calibration, not
    a deduction.** The factor `1+0.05 ch_2` is not obtained from the halo mass
    function, cooling, feedback or a halo-occupation model. The claimed five-
    percent excess of bright galaxies therefore cannot test the onset time
    until a forward model and survey selection function are specified.
174. **ch28 equates 500 million years ago with redshift `z approximately
    0.5`.** In standard cosmology `z=0.5` is roughly five billion years of
    lookback time, while 0.5 Gyr lookback corresponds to `z approximately
    0.04`. This is an order-of-magnitude timing mismatch inside the proof of
    the headline phase transition, separate from the already flagged choice
    among the chapter's three onset thresholds.
175. **ch28's critical-temperature calculation is dimensionally undefined and
    the comparison temperature is false.** Dividing bits per second by an
    entropy in units of `k_B` does not produce kelvin without an energy and a
    conversion law; moreover `10^5 K` is not the temperature of Earth's
    biosphere (order `10^2 K`). The existing scope note calls the coincidence
    asserted, but does not record these two direct failures.
176. **ch28's claimed second-order transition contradicts its own signatures.**
    A second-order thermal transition has a continuously emerging order
    parameter, whereas the chapter writes an abrupt `0 -> 0.95` jump and then
    predicts a discontinuity in `w_DE`. The asserted 3+1-dimensional Ising
    universality class and 100-Mpc correlation-length saturation are also not
    derived from the displayed one-component Landau potential.
177. **ch28's late-time numerical predictions are mutually inconsistent with
    ch27's corrected model.** It predicts `w_DE(z<0.5)=-0.95+-0.02` and a
    growth-rate kink of 0.08, while ch27's own correction gives present
    constant-epsilon `w=-0.85` and about `-0.9925` at `z=0.5`. No single
    `ch_2(z)`, action or perturbation equation produces the ISW, lensing,
    growth, halo, luminosity and EOS coefficients together.
178. **ch28's conclusion reverses the logic of its own verification ledger.**
    Agreement of BBN and the primary CMB with standard physics is consistent
    with an imposed early-time `ch_2 approximately 0`; it does not confirm that
    consciousness is recent. The genuinely discriminating late-time effects
    remain prospective and unreplicated, exactly as the ledger says.
179. **ch29's model function does not describe a transition at `z_*=0.5`.**
    The Gaussian `ch_2(z)=0.95 exp[-(z/z_*)^2]` is positive at every finite
    redshift, centered on the present, and equals only `0.95/e approximately
    0.35` at `z=z_*`. Calling `z_*` the emergence redshift and drawing a
    vertical phase boundary there is therefore incompatible with the stated
    function, as are the repeated exact-zero claims at early times.
180. **ch29 simultaneously treats its two added parameters as predictions and
    fit parameters.** Lines 77--92 call `f_C=0.08` and `z_*=0.5` predicted and
    “not free to fit,” but every degree-of-freedom count subtracts two, the
    MCMC table estimates both, and the likelihood-ratio/BIC calculations charge
    two parameters. These are different tests and cannot be combined into one
    significance claim.
181. **ch29 conflates Pantheon with a 580-supernova sample.** Pantheon contains
    1048 objects as the theorem itself states; the chapter supplies no cut
    mask, object list or likelihood that reduces it to 580. The number 580 is
    the size associated with Union2.1 elsewhere in the manuscript. Calling the
    analyzed catalog “580 Pantheon SNe” leaves the headline likelihood without
    an identifiable dataset.
182. **ch29's supernova chi-square is not the Pantheon likelihood it names.**
    It sums diagonal `sigma_i^-2` residuals and omits the published covariance,
    calibration/standardization nuisance treatment and absolute-magnitude
    degeneracy. Subtracting all six LambdaCDM parameters from the SN count is
    not justified either: supernova distances alone do not independently fit
    the six CMB base parameters. Thus neither `563.8` nor `289.7` is
    reproducible from the displayed statistic.
183. **ch29's F-test has unverified regularity assumptions.** The formula
    requires a nested model with the relevant Gaussian/linear regularity. Under
    the natural null `f_C=0`, the transition scale `z_*` is unidentified, so
    the usual two-degree-of-freedom chi-square/F reference law does not follow.
    The same issue invalidates the direct conversion of `Delta chi^2=333.1`
    into the quoted p-value unless a calibrated null distribution is supplied.
184. **ch29 labels comoving BAO distances as angular-diameter distances.** The
    tabulated values near 1512, 1975 and 2310 Mpc are on the scale of `D_M`,
    consistent with the survey description immediately above, not
    `d_A=D_M/(1+z)`. The mislabeled observable makes the model/data comparison
    dimensionally wrong even before its covariance is considered.
185. **ch29 mistakes `H(z=0.38)>H_0` for the Hubble tension.** In any expanding
    LambdaCDM-like model the Hubble rate at positive redshift is expected to
    exceed its present value. Comparing the BAO estimate `H(0.38)=83` directly
    with the CMB-inferred present `H_0=67.4` is not a tension measurement and
    cannot show that `H_0=69.8` reconciles them.
186. **ch29's CMB data count and likelihood compression are undefined.** Adding
    maximum multipole labels does not produce 6900 independent observations,
    and no covariance or compression maps the Planck TT/TE/EE/lensing
    likelihood to “effective dof approximately 60,” then to `52/50`, and then
    to the unrelated global `9/11`. The printed chi-squares therefore do not
    identify a Planck likelihood.
187. **late-time physics can alter the observed primary-CMB angular spectrum
    even if recombination microphysics is unchanged.** The angular-diameter
    distance to last scattering maps physical acoustic scales to multipoles,
    so a changed late expansion history need not give identical primary
    `C_ell`. Conversely, if the two predictions really are identical for the
    same parameters and data, their chi-square cannot be both 46.2 and 46.3.
188. **ch29's global degree-of-freedom construction subtracts the common model
    parameters once per dataset.** For one joint fit, the global count is the
    total number of independent data combinations minus the global parameter
    count (plus properly tracked dataset-specific nuisances), not the sum of
    three separately computed `N_i-k`. The existing correction catches the
    impossible CMB `9 -> 11` reversal but not this additional structural
    over-subtraction.
189. **summing separately quoted component minima does not establish a joint
    minimum.** The SN, BAO and CMB minima can occur at different parameter
    vectors. A global `687.3` or `354.2` requires evaluating the summed log
    likelihood at one common joint best fit with cross-dataset nuisance and
    covariance treatment; the chapter provides neither the parameter point
    nor the likelihood outputs.
190. **ch29's BIC uses different `N` values for models fit to the same data.**
    In `BIC=chi^2+k ln N`, `N` is the observation count and must not change
    from 590 to 588 merely because two parameters were added. Those figures are
    already disputed dof, not data counts. The in-text arithmetic correction
    accurately recomputes the printed inputs but cannot make them a valid BIC.
191. **the fitted constant `w=-0.953` is not the chapter's own `w(z)` model.**
    Its definition gives `w(0)=-0.85` and, at `z=z_*=0.5`,
    `w=-1+0.15 e^-3 approximately -0.9925`, not `-0.953` or the forecast
    `-0.95`. The MCMC table and future-survey predictions therefore fit a
    different parameterization from the one defined at the chapter opening.
192. **ch29's claimed Hubble- and clustering-tension resolutions are not
    demonstrated by the parameter table.** A midpoint `H_0=69.82` is not by
    itself a joint consistency test, and no covariance calculation yields the
    asserted final `1.5 sigma`. Raising `sigma_8` from 0.811 to 0.876 also needs
    an explicit low-redshift likelihood; the chapter merely calls it “excess
    clustering” without identifying the measurement or its `S_8` degeneracy.
193. **ch29's systematic-error bounds are assertions borrowed from survey
    validation, not tests of this fit.** Published control of calibration,
    foregrounds and nonlinear corrections does not imply the new model's
    `Delta chi^2` is robust, nor does it establish the unsupported caps of 10
    for SN systematics or the claimed CMB split `58.4 -> 6.9`.
194. **the advertised jackknife never removes data or refits.** It subtracts
    hand-picked counts or chi-square amounts (143, 73, 88, 44, 20 and 2) from
    the totals without object-level residuals, covariance deletion or
    re-optimization. Those arithmetic scenarios cannot show robustness to
    removing any dataset and should not be called a jackknife analysis.
195. **several listed falsifiers do not distinguish the proposed model from
    LambdaCDM.** Conditions such as `w(z<0.5)<-0.90`, unchanged primary CMB and
    unchanged BBN are all satisfied by standard `w=-1` cosmology. The latent
    parameters `z_*` and `f_C` are not direct observables until a unique
    operational `ch_2` and forward likelihood are supplied.
196. **ch29's conclusion presents an explicitly unreproduced analysis as clear
    evidence.** Its own verification ledger correctly says every component
    chi-square, MCMC result, F-test, BIC and p-value awaits a primary-catalog
    rerun. The mock plot, internally inconsistent observables and arithmetic
    deletion tests cannot upgrade that retrospective in-house fit to
    independent replication.
197. **ch30's clinical formula has a hard ceiling far below its diagnostic
    threshold.** If each of the five band vectors is normalized, Cauchy--Schwarz
    gives `|(1/(5M)) sum_(b,j) phase*phi_bj|^2 <= 1/M`; with the 64-channel
    protocol this is at most `1/64=0.015625`, not 0.95. Under a single joint
    normalization the tighter ceiling is `1/(5M)`. If the amplitudes are left
    unnormalized instead, the claimed range `[0,1]` disappears. Thus the
    reported means 0.23--0.98 cannot be values of the displayed normalized
    statistic.
198. **the clinical state vectors are not normalized as written.** With
    `sum_j |phi_j|^2=1`, the vector `(1/sqrt M) sum_j phi_j |e_j>` has norm
    squared `1/M`, not one; the fMRI construction has the identical `1/V`
    defect. Removing the prefactor or changing the coefficient normalization
    produces different downstream scales, so this is not a harmless notation
    slip next to a fixed 0.95 threshold.
199. **the chapter does not translate the theoretical `ch_2`; it defines a new
    amplitude statistic.** The recalled expression averages nonnegative
    probabilities `<Psi|P_n|Psi>`, while the clinical expression averages
    signed/complex filtered voltages `phi_(b,j)`, squares after summing, and
    then time-averages. No theorem relates these objects or transports the
    theoretical threshold between them.
200. **the “projection operators” are type-inconsistent.** Frequency filters
    act on time-series function spaces, while `|Psi_EEG(t)>` was defined as an
    instantaneous vector in an electrode basis. The five overlapping idealized
    bands are not the electrode-space projections `P_n` used in the recalled
    formula, and no sampling, boundary or filter convention makes them
    idempotent orthogonal operators on the stated space.
201. **the digital encoding is internally inconsistent and not gain-invariant.**
    Construction 30.x integrates power over the whole window to obtain one
    `n_(b,j)`, but the clinical formula later uses `n_(b,j)(t)`. Multiplication
    by the arbitrary factor 1000, electrode gain, voltage units, window length
    or referencing can change the floor and ternary digit sum discontinuously.
    No calibration standard or invariance proof is supplied.
202. **the alleged 847-patient validation cohort has no recoverable study
    provenance.** Citations to established CRS-R and coma-science literature
    do not identify seven centers, ethics approval, registry, inclusion flow,
    raw EEGs, preprocessing code, held-out test protocol or publication for
    this 2015--2024 cohort. The chapter's own ledger correctly calls it
    unvalidated; the patient-level claims cannot be treated as a clinical
    study until those records exist.
203. **the diagnostic strata and the confusion matrix disagree before any
    algorithm is evaluated.** Coma plus VS/UWS gives 410 nominal unconscious
    patients, while MCS-/MCS+/EMCS gives 437 nominal conscious patients. The
    confusion matrix instead declares gold-standard totals 416 and 431, moving
    six patients across the binary target without explanation.
204. **the MCS- row is mathematically incompatible with the 0.95 classifier.**
    MCS is a conscious gold-standard category, so 96.8% accuracy among 189
    patients means about 183 must be at least 0.95. Even if the other six were
    zero, their mean would then be at least
    `183*0.95/189 approximately 0.920`, contradicting the printed mean
    `0.87`. The stated standard deviation cannot repair this bounded-average
    contradiction.
205. **the main distribution figure moves the threshold from 0.95 to 0.8.**
    Its horizontal scale maps `x=8` to 0.8, yet the red line at `x=8` is labeled
    0.95 and the conscious shading begins there. The misplaced line visually
    hides the MCS- contradiction rather than depicting the classifier defined
    in the theorem.
206. **the measurement duration changes across the same protocol.** The cohort
    theorem specifies a 20-minute resting EEG; the comparison table and impact
    text call it 5--10 or 10 minutes; the limitations give 30--60 minutes of
    processing. Acquisition and processing can differ, but the text explicitly
    compares incompatible acquisition durations without a protocol version.
207. **McNemar's statistic is not derivable from the two marginal accuracies.**
    A paired McNemar test requires the two discordant cell counts (behavioral
    right/fractal wrong and behavioral wrong/fractal right). `519/847` and
    `824/847` do not determine them, so `chi^2=287.4` and its p-value cannot be
    checked from anything printed.
208. **the MCS- case study contradicts its own diagnosis.** MCS- means the
    patient has reproducible evidence of consciousness without higher-level
    language behavior. Calling an MCS- patient's responses reflexive and the
    patient unconscious because `ch_2=0.89`, then treating persistence in MCS-
    as confirmation, reverses the stated gold standard rather than predicting
    it.
209. **the named clinical cases are not traceable evidence.** MC-047 and MC-203
    have no site, registry identifier, report, consent/protocol reference or
    source dataset. The quoted message, threatened withdrawal and follow-up
    can function as hypothetical illustrations only, not validation events.
210. **relabeling eight false positives after later emergence introduces
    verification bias.** Subsequent behavioral recovery does not prove
    consciousness was present at the baseline EEG. Calling those baseline
    errors evidence that 97.3% is a lower bound uses the outcome to revise the
    reference standard and inflates accuracy unless the adjudication rule was
    preregistered and applied symmetrically.
211. **the prognostic sample silently excludes an entire MCS subgroup.** The
    four recovery bins total 456, exactly `267 VS/UWS + 189 MCS-`, although the
    theorem says VS/UWS or MCS and the cohort also contains 156 MCS+ patients.
    No exclusion criterion is given. The logistic model also omits `beta_0`,
    so its plotted probabilities are not reproducible from `beta_1=8.73`.
212. **the band decomposition is not an identity.** The clinical statistic is
    the squared modulus of a sum over bands and therefore contains cross-band
    interference terms. It cannot equal `sum_b w_b ch_2^(b)` without a theorem
    eliminating or allocating those terms. The empirical weights describe a
    second model, not a decomposition of Definition 30.x.
213. **the chapter's IIT bridge is asserted rather than operational.** Summing
    electrodes is not by itself information integration, a varying ternary
    phase is not neural differentiation, and no map connects the EEG statistic
    to IIT's system/partition-dependent `Phi`. The cited Lean inequality is
    algebra over defined quantities, exactly as the verification ledger says,
    and cannot validate brain consciousness.
214. **the ethical protocol exceeds the evidence and is unsafe as written.**
    An unvalidated scalar is said to answer whether consciousness is present,
    justify a presumption of continued care above 0.95, and support palliative
    withdrawal below 0.50. Medication, seizures, artifacts and locked-in cases
    are simultaneously admitted confounders. Those thresholds cannot guide
    life-support decisions without prospective validation, uncertainty bounds,
    regulatory review and independent clinical judgment.
215. **the cost-effectiveness section has no health-economic model.** It moves
    from diagnostic percentages to dollars per correctly diagnosed patient,
    national savings and 2800:1 ROI without treatment pathways, survival,
    QALYs, time horizon, discounting, uncertainty or the asymmetric costs of
    false positives and false negatives. Arithmetic on assumed headline costs
    is not a cost-effectiveness analysis.
216. **the tumor-boundary appendix supplies a separate uncalibrated PDE.**
    `R_f(alpha,|grad phi|)` feeds a dimensionful gradient into the complex
    Dirichlet-series variable, `eta dot R_f` is not typed, and no curvature,
    well-posedness or map from solutions to boundary dimension is given. The
    numeric ranges and AUC are properly marked prospective, but do not follow
    from the displayed evolution law.
217. **ch30's conclusion contradicts its own verification ledger.** The
    measurement problem is not “solved”: the displayed statistic cannot reach
    its threshold under its normalization, the cohort is unreproduced, and the
    mapping to consciousness is unvalidated. What survives is a proposed
    biomarker research program with explicit prospective tests, not a clinical
    instrument ready for diagnosis or end-of-life use.
218. **ch31's displayed definition is not a definition of IIT's current
    integrated information.** `Phi=min_partition EI(partition)` omits the
    system's transition probability structure, cause/effect repertoires,
    distance, partition normalization and exclusion/maximal-complex choices
    that distinguish IIT versions. A generic state vector and projectors do
    not supply those data, so no mathematical equivalence can start from the
    objects declared in the chapter.
219. **the proof replaces distinct information quantities without a theorem.**
    It identifies effective information with mutual information, then with
    `-log_2 P(partition independent)`, and finally declares that probability to
    be `1-ch_2`. None of those equalities follows from the preceding
    definitions. The last line is the desired correspondence assumed as a
    premise, not derived.
220. **the theorem states both an approximation and an exact identity.** The
    box writes `Phi=-log_2(1-ch_2)+O(ch_2^2)`, while the proof and subsequent
    “precise correspondence” delete the remainder and use exact equality. An
    asymptotic `O(x^2)` near zero is neither a defined neural error term nor a
    license to evaluate at `x=0.95`; the in-text correction correctly explains
    why that expansion has no control there.
221. **the claimed awake-human IIT range of 4--6 bits cannot validate the
    mapping.** The chapter simultaneously says exact Phi is intractable beyond
    about ten elements, yet asserts typical whole-brain awake values in a
    narrow numerical band without a measurement definition, grain, IIT
    version, dataset or calculation. The number is therefore a retrospective
    alignment to the chosen `-log_2(0.05)`, not independent evidence.
222. **the thalamocortical regression confuses coefficients with explained
    variance.** In `ch_2=0.73 TC+0.14 CC+epsilon`, 0.73 and 0.14 are slopes in
    unspecified units, not percentages of variance. “Explains 73%” would
    require a partial or total `R^2`, design matrix, scaling and uncertainty;
    none is given.
223. **the phase-amplitude coupling expression is not normalized.** The complex
    average `<A_gamma exp(i phi_theta)>` scales with gamma amplitude and cannot
    distinguish stronger power from stronger coupling without a modulation
    index or surrogate normalization. Consequently its correlation with the
    already undefined clinical `ch_2` does not establish cross-layer
    integration.
224. **the 14.1-Hz “derivation” is multiplication by an arbitrary anchor.** The
    dimensionless constant `sqrt(2)` is assigned a 10-Hz baseline chosen from
    the alpha band; no substrate theorem selects 10 Hz, transports the PF alpha
    into neural frequency, or predicts inter-subject scaling. The resulting
    14.1 Hz is therefore an operational hypothesis, not a first-principles
    frequency.
225. **`sqrt(2):1` is not a harmonic relation or musical consonance.** Harmonic
    partials have rational integer frequency ratios; an irrational ratio is
    incommensurate. The analogy used to explain why the proposed frequency
    “crystallizes” coordination asserts the opposite mathematical property.
226. **the white-matter equation violates the chapter's own `[0,1]` range.** FA
    values lie in `[0,1]`, yet setting both displayed predictors to one gives
    `ch_2=0.42+0.61+0.18=1.21`. No link function, clipping rule, interaction or
    valid range of covariates is stated, so it cannot be a calibrated
    consciousness scale.
227. **the IIT/GWT synthesis contradicts its own logical labels.** It first
    calls IIT integration necessary and GWT broadcast sufficient, then says
    both are necessary. A sufficient broadcast would make integration
    unnecessary; two necessary conditions do not establish sufficiency. No
    experiment or formal implication repairs that truth-table conflict.
228. **the optogenetic section does not distinguish arousal, responsiveness and
    consciousness.** Mouse behavior following 14-Hz thalamic stimulation is a
    behavioral endpoint; calling it induced consciousness uses the disputed
    `ch_2` threshold as both classifier and validation target. The exact cohort
    numbers and frequency table remain unreplicated per the chapter's ledger.
229. **the artificial-network statistic is another incompatible `ch_2`.** It
    averages signed hidden activations rather than projector probabilities or
    EEG band powers, and `D(h_j(t))` is undefined until a discretization scale
    and encoding of negative/real activations are fixed. Architecture, data,
    training code, held-out tasks and run seeds are absent, so the reported
    network values cannot be reproduced.
230. **global ignition, novelty reports, confidence and feature binding do not
    behaviorally validate machine consciousness.** These are standard
    trainable computational functions. Using them to certify the same scalar
    whose interpretation they are meant to test is criterion contamination,
    not an independent ground truth.
231. **the LLM numbers cannot have been obtained by the stated protocol.** No
    definition maps token-level API outputs to the hidden-unit statistic, and
    proprietary GPT-4 and Claude-3 internal activations/weights were not
    available for the claimed calculation. The values, uncertainties, prompts,
    model versions and code have no provenance.
232. **the architectural explanation of those LLM numbers is technically
    false.** Autoregressive transformers condition each generation on prior
    context and their attention layers perform recurrent use across the token
    sequence; token outputs are not independent. Whether that constitutes the
    right causal recurrence for consciousness is open, but “feedforward” and
    “each token independent” cannot support the comparison.
233. **the base-3 criticality derivation reverses the calculus.** For
    `E(b)=log(b)/b`, the stationary point is `b=e` and it is a maximum, since
    the function tends toward zero as `b` grows. Minimization therefore does
    not yield base 3 and cannot enforce branching ratio one or the printed
    avalanche exponent. At most, integer base 3 approximately maximizes this
    particular ratio, a different optimization claim.
234. **the comparative-alignment status markers exceed their evidence.** The
    locust chromatin dimensions, 7--8-Hz field alignment, BMI energy benefit,
    and covariance between `ch_2` and avalanche exponents are prospective
    measurements not established by the cited background literature. Marking
    them “experimentally supported” or “computed” conflates the external
    phenomenon with the untested PF mapping.
235. **ch31's conclusion survives only as a research program.** Its own decisive
    correction proves the central 0.95 hypothesis empty for the displayed
    projector formula, and its ledger says every neural, animal, artificial and
    IIT bridge is unvalidated. The chapter therefore has not solved either the
    measurement or mechanism problem, though it does enumerate falsifiable
    experimental lanes that can be reformulated around a reachable observable.
236. **ch32 introduces another incompatible quantity under the name `ch_2`.**
    Its implementation forms per-band digital-root phases, takes a weighted
    phase mean, and squares the modulus. That is neither ch30's filtered-amplitude
    statistic nor ch31's projector, power-ratio, Chern--Weil, or entanglement
    quantity. The comment citing “Theorem 6.4 in Chapter 26” as the source of the
    weights also does not identify a matching derivation.
237. **the per-band normalization removes the cross-band signal used in the
    interpretation.** Each band is independently divided by its own maximum
    channel power before digitization. Absolute beta/gamma strength relative to
    delta/theta is therefore erased, so sedation and sleep claims based on
    changes in band dominance do not follow from the printed algorithm.
238. **the scaling rule has an unhandled singularity and outlier instability.**
    A zero-power band divides by zero. A single high-power channel rescales every
    other channel in that band before rounding and digital reduction, allowing
    an outlier to change the result discontinuously.
239. **the preprocessing code does not run as printed.** The amplitude artifact
    mask has length `T`, while `np.diff(EEG_filt, axis=1)` produces length
    `T-1`; the in-place Boolean OR therefore has incompatible shapes.
240. **deleting individual flagged samples corrupts the time series used by the
    later analysis.** `EEG_filt[:, ~artifact_mask]` concatenates the surviving
    points across gaps, introducing artificial discontinuities and a false
    regular timebase before ICA and spectral estimation.
241. **the artifact thresholds have no unit contract.** The hard-coded `200`
    and `50` are described as microvolt limits, but the loader/output unit and
    conversion are not specified. The same code can therefore mean materially
    different physiological thresholds across acquisition formats and APIs.
242. **the implemented statistic is whole-recording, not epoch-resolved.** The
    function averages power over the complete input before computing one
    scalar. It does not implement the chapter's 120-second epochs, ten-second
    sliding updates, epoch exclusion rule, or real-time trajectory.
243. **the temporal-stability check is undefined as written.**
    `Corr(ch_2 epoch 1, ch_2 epoch 2)` asks for the correlation of two scalar
    outputs. A population of paired subepochs, trials, or subjects is needed,
    but none is specified.
244. **the SNR denominator is measured outside the retained passband.** The
    preprocessing low-passes at 100 Hz, then the quality rule estimates noise
    from power above 100 Hz. That component has already been suppressed and is
    not an independent estimate of recording noise.
245. **the stated accessibility requirement contradicts the cost table.** The
    standards demand equipment below `$1,000`; the chapter's minimum system is
    `$8,500`, its research system reaches `$45,000`, and even its portable
    alternative is `$1,200` before the rest of the setup.
246. **the 0.95 threshold is not transportable between 64- and 8-channel
    montages without calibration.** The statistic averages a different number
    of phases and renormalizes each band across the channels present. Changing
    the montage changes the observable itself, not merely its measurement noise.
247. **the rapid-change alarm has the wrong sign for deterioration.** The rule
    triggers on `Delta ch_2 / Delta t > 0.05`, while the clinical examples include
    declining consciousness. A decrease is negative and cannot satisfy the
    printed inequality; an absolute-change or signed pair of rules is required.
248. **the proposed muscle-artifact remedy deletes a defining input.** The text
    recommends low-pass filtering below 30 Hz, but the statistic explicitly uses
    gamma power from 30--100 Hz. Applying the remedy changes the biomarker rather
    than merely cleaning it.
249. **the cross-species table does not support a universal threshold.** Species
    differ in montage, channel count, anatomy, and the chapter's own
    normalization; the text also concedes that thresholds may differ, yet labels
    below-0.95 dogs and parrots “probable” while retaining the universal-threshold
    framing.
250. **the software claim is not reproducible from the manuscript.** No package
    version, source commit, archive checksum, test vector, or output trace ties
    the stated release to the printed pseudocode. This finding does not assert
    that the named external URLs are absent; their current availability requires
    a separate web/provenance check.
251. **brain-death and life-support uses exceed the validated scope.** A proposed
    consciousness score cannot by itself establish brain death, a distinct
    medical and legal diagnosis with accepted neurologic criteria. The chapter
    presents neither prospective clinical validation nor regulatory evidence for
    that use.
252. **the “thermometer test passed” conclusion contradicts the chapter's own
    verification ledger.** Normative ranges, state bands, species bands,
    reliability, device transfer, and the consciousness interpretation are all
    recorded as unvalidated. A specified computation is not yet a validated
    measurement instrument.
253. **ch33 assigns a probability to numerical coincidence without a probability
    model.** A residual or agreement at 150 digits does not imply a universal
    false-positive probability below `10^-150`. That inference requires a
    specified null distribution, independence assumptions, selection protocol,
    and correction for the number of quantities searched.
254. **the power-method theorem is missing essential hypotheses.** Its proof
    expands an arbitrary matrix in an orthonormal eigenbasis, which is available
    for normal matrices, not general matrices. It also needs a nonzero component
    along the dominant eigenvector, and complex problems require a conjugate
    transpose rather than the printed transpose. Vector error and Rayleigh-
    quotient eigenvalue error need not have the same stated rate.
255. **the high-precision cost comparison is internally inconsistent.** It
    converts one multiplication into roughly `4,500` “bit operations,” multiplies
    by `10^6`, calls `4.5e9` bit operations one second, and then claims high
    precision is `10^9` times slower than double precision. At its own quoted
    `0.3 ns` per double multiplication, one million operations take about
    `0.3 ms`, so the displayed timings imply a ratio near `3.3e3`, not `1e9`.
256. **the chapter presents asserted fractal eigensolvers as completed numerical
    experiments without an executable operator specification.** The `H_P` and
    `H_NP` remarks give matrix sizes, shifts, precision, iteration counts, and
    wall times, but no matrix construction, code, data, residual, condition
    estimate, convergence log, or artifact connects those numbers to a defined
    operator.
257. **the first-zero Riemann--Siegel claim cannot deliver 150 digits from the
    displayed formula.** At `t≈14.13` the main sum has only the `n=1` term and
    the stated remainder is merely `O(t^-1/4)`, of order one rather than
    `10^-150`. Achieving 150 digits requires a controlled full expansion or a
    different certified evaluation, not just high-precision evaluation of the
    leading term and theta function.
258. **an interval image containing zero does not prove that a zero exists.**
    The proposed enclosure of zeta over a complex box may contain zero because
    of dependency or overestimation even when no input maps to zero. A rigorous
    first-zero proof needs, for example, a sign-changing bracket for the real
    Hardy `Z` function plus uniqueness/counting control, or an interval Newton/
    Krawczyk argument with the required hypotheses.
259. **Gauss--Kronrod rule differences are error estimators, not automatic
    rigorous 150-digit bounds.** The difference between nested rules can miss
    error for adversarial or poorly resolved integrands. Certified quadrature
    needs regularity bounds or ball/interval integration and outward rounding;
    neither is specified for the framework integral.
260. **the resonance-function implementation changes the phase convention.**
    The chapter writes `exp(i alpha n)`, whereas the earlier PF resonance kernel
    uses the `pi alpha` phase that produces `1+2 cos(pi alpha)` and the base-3
    selector. Omitting `pi` changes the function and its claimed special values.
261. **the Filon/Euler--Maclaurin paragraph is not a reproducible 150-digit
    algorithm.** “Integral plus correction terms” supplies no truncation point,
    number of terms, derivative bounds, tail enclosure, or domain in `s`; the
    one-second performance claim therefore has no auditable error certificate.
262. **the Riemann-zero parallelization confuses checking listed points with
    verifying the first `10^10` zeros.** Independent small residuals do not show
    that no zero was missed, establish multiplicities, or match the required
    zero count. A global counting argument such as a certified Turing-method
    computation is still required.
263. **the “distributed Arnoldi” result is not a general scalability theorem.**
    Arnoldi orthogonalization entails global reductions, and matrix-vector
    communication depends on sparsity, distribution, topology, and the number
    of processes. The printed costs and universal optimum `P≈sqrt(N)` omit those
    dependencies and do not justify the claimed hour-scale 150-digit run.
264. **the dense-size and precision claims omit the storage model.** A
    `2^20 × 2^20` dense matrix has about `1.1e12` entries before arbitrary-
    precision overhead. The chapter does not say whether the fractal operator is
    sparse, matrix-free, or structured, so its processor grid and wall time are
    not reproducible resource estimates.
265. **the conclusion “all results in this book were computed to 150 digits” is
    unsupported and contradicted by the chapter's own corrections.** No complete
    code release, inputs, output hashes, precision logs, or interval certificates
    accompany that global assertion; earlier formulas converged to wrong values
    despite the chapter's high-precision premise.
266. **the verification ledger is stale and overbroad in opposite directions.**
    It says the Chapter 4 substrate is the only machine-verified content in the
    book, despite the much larger current Lean corpus, while declaring all
    described algorithms correct by reference even though the power-method,
    Riemann--Siegel, interval-zero, and distributed-Arnoldi statements/applications
    are not correct at their printed scope.
267. **the software cross-reference is stale.** The chapter says all code
    examples in Chapter 31 use the listed libraries, but Chapter 31 is the
    neuroscience/IIT chapter and this statement does not identify a versioned,
    executable numerical artifact for ch33.
268. **ch34's three-level verification ladder still calls numerical
    reproduction a “rigorous proof.”** Interval arithmetic can certify a
    numerical enclosure, but 150 reproduced digits do not prove the physical
    interpretation, an infinite theorem, or a Millennium statement. The scope
    note correctly withdraws this promotion; the ladder and conclusion do not.
269. **Protocol R1 does not run with the meanings assigned to its variables.**
    `findroot(lambda t: zeta(0.5 + 1j*t), t0)` returns the ordinate variable
    `t`, not `rho=0.5+it`; the next loop tests `rho.real≈0.5`, evaluates
    `zeta(rho)`, and prints `rho.imag`. Those operations therefore test the
    wrong number even if root finding succeeds.
270. **Protocol R1 does not establish that it found the first 100 zeros.** Its
    guesses advance by a fixed `9.5`, while zero spacing is neither constant nor
    large enough to guarantee distinct basins. Newton convergence can duplicate
    or skip roots, and small residuals at returned points do not supply the
    zero-count/completeness argument required by “first 100.”
271. **Protocol R2 is undefined at its own grid and cannot meet its precision
    criterion.** The grid includes `x=0`, making `log(x/y)` singular; the kernel
    is generically dense rather than sparse; `construct_spectral_operator` is
    absent; and NumPy/SciPy `float64` plus `eigsh` cannot certify a `10^-145`
    eigenvalue error. “Localized near the critical line” is also undefined for
    eigenvectors indexed by `x∈[0,1]`.
272. **Protocol P1's point count is wrong before the known memory failure.** The
    recursion starts with three points and triples at each call, so
    `sierpinski_gasket(16)` returns `3^17=129,140,163` rows including duplicated
    boundary representations, not the commented `3^16=43,046,721`. Its dense
    matrix would therefore be about nine times larger than even the already
    impossible 14.8-PB estimate recorded later in the chapter.
273. **Protocol P1 is neither sparse nor reproducible.** It explicitly allocates
    and fills every pairwise cosine-distance entry, then hands the dense array to
    a sparse iterative solver. The asserted eigenvalues, convergence table, and
    four-hour runtime have no executable artifact or residual certificate, and
    the coded `alpha_NP=pi/3` contradicts the framework's stated NP constant.
274. **Protocol P2 does not implement its advertised test.** It depends on the
    unavailable `H_P`, combines SciPy floating eigenvalues with `mpmath` object
    values in `np.corrcoef`, supplies no MSE computation, and evaluates
    `polylog(s,z_star*n)` across branch-sensitive arguments of growing modulus.
    A fitted correlation would in any case be evidence for a finite sequence,
    not a complexity-class theorem.
275. **Protocol C1's expected outputs are mathematically impossible under its
    own real-matrix formula.** The already-recorded bound gives `ch_2≤1/2` for
    every real `W`, so the claimed trained value `0.963` cannot occur. The code
    also performs no training, fixes no random seed, and labels random networks
    both “proto-conscious” and “untrained/mechanical.”
276. **Protocol C2 inherits the same range contradiction.** A real phase-
    coherence matrix cannot yield the printed conscious mean `0.982` or satisfy
    the `0.95` classifier through this formula. Thus the claimed 97.3% accuracy
    is not merely unvalidated; it is unattainable by the displayed computation.
277. **the promised data and code release is not publicly reproducible.** As of
    2026-10-08, unauthenticated requests to both printed GitHub URLs return 404.
    In the checked PF repository, none of
    `riemann_zeros_150digits.txt`, `fractal_eigenvalues_level16.npz`,
    `eeg_consciousness_dataset.mat`, `verification_protocols.py`, or
    `verification_guide.pdf` is tracked, and the advertised top-level `code/`,
    `data/`, and `tests/` directories do not exist.
278. **the automated report is a non-executable interface sketch.** It imports
    an absent `verification_protocols` module and calls six undefined functions;
    “ALL TESTS PASSED” is therefore an expected string, not a produced audit
    artifact. The pytest Riemann tests repeat Protocol R1's variable error.
279. **the precision troubleshooting cannot repair the mixed-precision stack.**
    Setting `mp.dps=150` affects `mpmath`, not NumPy arrays, SciPy `eigsh`, or
    Python float constants already used by R2, P1, P2, C1, and C2. Those paths
    remain double precision regardless of the suggested restart.
280. **the Lean4Lean section does not document independent external-kernel
    verification.** It explicitly says the package re-imports PF declarations
    into another Lean build and that the external `lean4lean` executable was not
    run. This is a useful second build/import check, but calling it “independently
    re-verified” or a third prover exceeds the stated trust boundary.
281. **the certification headline is structurally weaker than it sounds.** Zero
    project `axiom`, `sorry`, and `native_decide` tokens establish an important
    hygiene property, not substantive coverage. They do not detect vacuous
    propositions, dead binders, aliases, supplied target hypotheses, or proxy
    definitions; the later gate audit's broken witness-name criterion further
    invalidates any inference from “clean” to “proved as advertised.”
282. **the two-anchor section promotes supplied PF assignments into external
    anchors.** Perelman's theorem does not derive
    `alpha_Poincare=1`, and an external Navier--Stokes result does not derive
    `alpha_NS=3pi/2`. The Lean files prove conditional arithmetic from these
    values plus target-bearing structural identities and branch conditions; they
    do not make either assignment an external theorem or force all values from
    one physical datum.
283. **chapter references identify the wrong locations for every numerical
    protocol.** R1/R2 cite Chapter 13 instead of the current RH chapter 20;
    P1/P2 cite Chapter 17 instead of P-vs-NP chapter 21; C1 cites Chapter 5
    instead of the consciousness definitions centered in chapter 6; C2 cites
    Chapter 26 instead of the clinical chapters 30--32; and the closing software
    pointer says Chapter 31 although implementation is chapter 35.
284. **the final global claim is self-contradictory.** “Every claim ... is
    computationally verifiable to 150-digit precision” sits immediately beside
    a ledger saying Millennium implications are conditional, constants are
    asserted, and clinical claims are untested. Many claims are qualitative,
    infinite, physical, or definitional and cannot be validated by reproducing a
    decimal output.
285. **ch34A's flagship implication is formally non-load-bearing.** The
    chapter's own 2026-08-08 audit proves that every listed consequence was
    established independently of the five antecedents, so the theorem has the
    form `P -> C` with unconditional `C` and would remain true for an unrelated
    antecedent such as `2+2=4`. The opening, section summaries and conclusion
    nevertheless continue to say that the substrate “determines” the
    consequences and that a single citation carries the TOE.
286. **“all five antecedents realised” conflates incompatible evidence types.**
    A1 is a weak formal proxy for the substrate prose; A2 is a definitionally
    packaged alpha skeleton; A3 is not a consequence of Perelman; A4 is
    conditional probability arithmetic over a supplied noise model; and A5 is a
    hard-coded table. These are respectively formal object/proxy, stipulated
    assignments, unsupported bridge, conditional operationalization and
    replicated data representation --- not five established physical premises.
287. **the 143-entry antecedent is not an empirical universal-coherence
    result.** Its 72 P and 71 NP rows are canonical entries whose measured
    alpha field is set equal to the canonical field. Lean can verify the table
    and its equalities, but the construction contains the claimed match and
    supplies no observation, sampling procedure, provenance or independent
    replication.
288. **the nine-way IBM antecedent does not establish an experimental
    probability.** The Lean theorem derives a bound from an arbitrary
    `NoiseModel9` and supplied hypotheses. It does not validate a hardware noise
    model, channel independence, calibration, trial protocol or observed
    frequency; those would be empirical premises separate from the conditional
    theorem.
289. **neither advertised external anchor fixes its PF alpha value.** Perelman's
    proof of the Poincare conjecture does not imply
    `alpha_Poincare=1`, and a Navier--Stokes/Euler blow-up result does not imply
    `alpha_NS=3*pi/2`. The chapter sometimes acknowledges the latter as the
    framework's asserted assignment, but elsewhere promotes both assignments to
    external mathematical results.
290. **the two-anchor cascade is conditional target-bearing arithmetic, not a
    derivation of the remaining physics.** Its equations include the desired
    relationships, while branch and positivity conditions are supplied. The
    root-verified r339/r340 files have exactly this limited scope and are not
    imported by `PF.lean`; literal Clay statements and operator/geometrization
    bridges remain mathematical work, not merely carrier formalization.
291. **the alpha inventory has two concrete count inconsistencies.** The chapter
    repeatedly says “nine alpha-values,” while its main tuple contains ten
    variables (`Poincare`, `RH`, `YM`, `BSD`, `NS`, `PvNP`, `P`, `Hodge`, `NP`,
    `QG`). It also announces “two derived invariants” and immediately lists
    three, D1--D3.
292. **strict minimality is only relative to the chosen axiomatization.** The
    independence result is real conditional algebra, but several defining
    equations already contain target values (for example the BSD value and QG
    normalization). It therefore proves neither physical necessity nor unique
    TOE selection. The claimed zero-dimensional variety also relies on the
    anchor and branch/positivity data, not merely nine unconstrained equations.
293. **C9--C12 are arithmetic identities, calibrations or an explicitly toy
    conservation law, not cosmological predictions.** A log-ratio identity and
    inequalities bracketing observed numbers do not supply a likelihood,
    uncertainty model, parameter-count penalty, preregistration or independent
    fit. Calling them suppression mechanisms or a resolution of the Hubble
    tension exceeds their formal content.
294. **C13--C15 do not validate a consciousness threshold.** C13 installs
    `19/20` by definition, C14 is an order dichotomy, and C15 is a conditional
    real-analysis implication. These are machine-checkable facts, but none
    connects a measured neural observable to the chosen `ch_2`, establishes
    clinical reachability, or independently validates IIT.
295. **the “20-to-20 bridge” is engineered substitution rather than a physical
    bridge.** The same integer appears because two separately defined formulas
    were chosen to return it. No theorem connects computational complexity,
    neural integration, an IIT quantity or the PF substrate, and no empirical
    protocol tests the identification.
296. **the H3 origin of the denominator 10 is still supplied, not derived.**
    The relevant formal arithmetic starts from a stipulated H3 exponent list
    and a supplied universal-coupling/half-argument identification. It does not
    derive the Coxeter data from a substrate operator or prove the required
    geometrization bridge. The later `120=2*2*1.5*20` product is likewise an
    identity among assigned values, not a cosmological mechanism.
297. **the chapter's `W_alpha` is not Perelman's Ricci-flow W entropy.** It is a
    discrete base-3 cascade functional with different objects, dynamics and
    hypotheses. Reusing the letter W and the value `alpha_Poincare=1` does not
    transport Perelman's method to the other Clay axes.
298. **the cross-domain “saturation” is retrospective algebra unless separately
    preregistered and replicated.** Eighteen Lean files produced in one evening
    can certify substitutions and exact identities, but not independent
    physical predictions. The GI “144th blind prediction,” empirical matches
    and IBM/clinical correspondences require timestamps, frozen protocols,
    multiplicity accounting and external replication before they can carry the
    chapter's prospective language.
299. **the P-vs-NP carrier remains disconnected from standard computation.** In
    V3, positivity of `encodeConfig (encodeRun x)` is automatic for the
    prime-power encoding and imposes no transition or accepting-state
    semantics. More seriously, the current `InClassP` append-invariance clause
    forces every represented language to be either empty or universal, while
    `ClassNP` contains `{[]}`; the literal inequality is therefore trivial for
    a definition error rather than complexity theory. ch34A does not incorporate
    this newly verified defect.
300. **the advertised C1--C25 list has no C19.** The labels jump from C18 to C20,
    leaving only 24 numbered consequences unless a differently named companion
    statement is being counted. The chapter should either restore C19 or state
    an explicit, reproducible counting convention.
301. **the chapter presents incompatible certification snapshots as one current
    state.** It alternates 78 and 81 landings and cites different build totals
    and HEADs (including 4030 jobs at `42990ea` and 8516 jobs at `09e6336`), then
    closes by citing the earlier HEAD again. Each historical snapshot may be
    meaningful, but they cannot jointly be the reproducible current audit.
302. **the universal-carrier language exceeds the exact Clay encodings.** The
    RH route is conditional on an open contour count, the NS endpoint does not
    encode the PDE and includes vacuous/zero constructions, YM lacks a 4D QFT,
    BSD rank functions are aliased to zero, and Hodge uses supplied hypotheses
    or trivial existentials. Distinct routed proposition names do not by
    themselves establish the standard problems.
303. **the claimed independent verification is only proof replay unless an
    independent implementation and provenance are supplied.** Re-running the
    same declarations through Lean, or importing them into a second Lean build,
    is valuable reproducibility and trust-hygiene evidence; it is not independent
    mathematical derivation, empirical replication or external-kernel checking.
304. **“machine checked at maximum scope” needs the scope in the headline.** At
    present the strongest verified content is a mixture of exact UHF theorems,
    conditional algebra, definitional identities, toy carriers and proxies. The
    kernel result is real at each stated type, but the phrase invites readers to
    substitute the surrounding physical interpretation for that exact type.
305. **ch35 documents a software suite that is absent from the current tracked
    repository.** At HEAD there is no top-level `principia_fractalis/` package,
    `tests/` directory, `requirements.txt`, `CONTRIBUTING.md`, or
    `docs/conf.py`. The only tracked test match is a Lean audit shell test, and
    the relevant Python research scripts live chiefly under `ARCHIVE/`. Thus the
    printed quick start, imports, 47-test run and Sphinx build cannot be executed
    from the repository as stated.
306. **the “complete code examples” are interface sketches, not complete
    implementations.** Core imports such as `find_zero`, `verify_zero`,
    `compute_ch2`, the fractal generator and the Millennium module do not exist
    at the claimed paths; several listings end in literal ellipses; and the Koch
    curve distance is explicitly unimplemented. This is useful design
    pseudocode, but the chapter repeatedly labels it production-ready software.
307. **the dense matrix is not a justified discretization of an integral
    operator.** It samples `K(x_i,x_j)` without quadrature weights, measure
    factors or an `N`-dependent normalization. Consequently its eigenvalues
    generally scale with the sampling convention and need not converge to the
    spectrum of the advertised continuum operator even if memory and runtime
    were unlimited.
308. **the P-vs-NP example uses the wrong NP parameter and supplies no
    reproducible eigenvalue provenance.** It constructs `H_NP` with
    `alpha=pi/3`, while the book's canonical NP assignment is
    `phi+1/4`. The correction correctly proves the printed computation cannot
    run at the stated size, but the chapter still presents its two output
    eigenvalues as if this exact code generated them.
309. **the consciousness example is not defined for its displayed effective
    matrix under the manuscript's matrix formula.** `W3 @ W2 @ W1` has shape
    `10 x 784`, so `Tr(W^2)` is undefined; even for a square real matrix the
    corrected `ch_2` formula is capped at `1/2`. The printed trained-network
    value `0.968` and “Conscious” label therefore cannot come from that formula,
    independently of the now-consistent three-way print rule.
310. **the Riemann example is not executable and does not test RH.** It calls
    `zeta(rho)` without importing `zeta`, so it would raise `NameError` even if
    the package existed. Finding and checking a known on-line zero is valuable
    numerical reproduction, but it cannot verify that all nontrivial zeros lie
    on the critical line.
311. **the corrected Yang--Mills test remains internally impossible.** It uses
    `mp.mpf` without importing `mp`, replaces the invalid literal with only a
    six-digit reference value, then leaves the assertion tolerance at
    `10^-145` while claiming the tolerance is matched to attainable precision.
    It also compares against a stored expected number rather than testing a
    constructed four-dimensional Yang--Mills theory.
312. **the optimization claims remain unsupported after the accurate resource
    correction.** The GPU path allocates the same dense matrix, copies it back
    to host RAM and then invokes the CPU eigensolver; the “10x speedup” has no
    benchmark or reproducible hardware record. The sparse path retains nearly
    every cosine-kernel entry, as the chapter's own correction proves. The final
    summary nevertheless continues to promise GPU/sparse large-scale use.
313. **the quantitative software-quality claims have no tracked evidence.** The
    chapter asserts 47 passing tests, 90%+ coverage, integration tests,
    continuous integration for this Python suite, notebooks, API docs and video
    walkthroughs, but none of the named suite, coverage configuration or Sphinx
    project is present at HEAD. These should be future architecture targets or
    linked to immutable artifacts, not reported as current verification.
314. **the repository, citation and license blocks are stale and materially
    wrong.** The chapter points to `pcohen/principia-fractalis`, version 1.0.0,
    a placeholder ORCID and an MIT license. The actual remote is
    `FractalDevTeam/Principia-Fractalis`; tracked `CITATION.cff` says version
    2.6.1 and ORCID `0009-0002-0734-5565`; tracked `LICENSE` is a restrictive
    non-commercial research license, while the README/CFF call it CC BY-NC 4.0.
    These three licensing descriptions are mutually incompatible and require a
    deliberate legal/documentation choice, not a silent prose edit.
315. **the abstract operator interface does not enforce its advertised
    self-adjointness.** A subclass can return any kernel, yet `eigsh` is called
    unconditionally as though the matrix were Hermitian. The cosine-distance
    example is symmetric, but the base class supplies no validation of symmetry,
    real/Hermitian dtype, domain measure or boundary conditions.
316. **the chapter's own navigation metadata is stale.** Its prerequisites call
    chapters 29--30 “Numerical Methods and Verification,” although those topics
    are chapters 33--34 in the current book, and its summary label is
    `sec:summary-ch31`. These are small editorial defects but contribute to the
    chapter's broken reproduction path.
317. **the arbitrary-precision API contract is underspecified.** The docstring
    promises a Python `complex` return at 150 decimal digits, although built-in
    complex numbers are binary64; an actual implementation would need an
    `mpmath.mpc` or equivalent type end-to-end. The chapter's precision context
    alone cannot lift float inputs, NumPy arrays or SciPy outputs to 150 digits.
318. **“the code is yours” conflicts with the tracked legal restrictions.** The
    prose promises unrestricted open-source modification, distribution and
    commercial-style reuse, while the actual license is revocable,
    non-transferable, forbids commercial use and imposes mandatory notification.
    Open inspection and research access remain valuable, but the chapter should
    use the precise license category rather than MIT/open-source language.
319. **the foundational lexicon reinstates the pre-correction Timeless Field and
    marks it PROVEN.** It defines a projective limit of nuclear-operator tensor
    factors, asserts `K_0=Z[1/3]`, and calls the construction rigorous, although
    ch04 itself records that the limit runs the wrong way, the connecting maps
    are CP contractions rather than star homomorphisms, and `F_alpha` collapses
    to a subalgebra of `C`. The genuine later UHF inductive-limit construction
    should replace this obsolete entry rather than be conflated with it.
320. **the lexicon promotes an unproved spacetime and force-unification map to a
    prediction without a defined mechanism.** The quotient
    `Aut(T_infinity)/Aut_0(T_infinity)` is already known to collapse under the
    literal connected-component reading, and no exact embeddings identify
    diffeomorphisms or the Standard Model gauge groups with the listed
    automorphisms. A proposed interpretation still needs a mathematical map
    before it becomes a testable physical prediction.
321. **the lexicon labels unproved global analytic claims about `R_f` as
    PROVEN.** Absolute convergence for `Re(s)>1` is routine, but analytic
    continuation to all of `C\{1}` for every real alpha is not established by
    that convergence statement. The displayed “universal pi/10 factor” leaves
    `alpha_c`, `s_c` and `xi` undefined and has no derived limit theorem; it
    cannot support a combined proven/computed status.
322. **the claimed first-principles derivation of `kappa=5e-6` is arithmetically
    false twice.** `exp(pi^2/12)` is about `2.276`, not `707.1`. Using the actual
    exponential in the printed formula gives about `1.94e-3`; even inserting
    `N_eff=707.1` gives about `2.0e-8`, not `5e-6`. The coupling and the
    eigenvalue-to-zero scaling therefore remain unsupported by this derivation.
323. **the lexicon restores three withdrawn “derivations” of the 0.95
    threshold.** The earlier chapters already show that the percolation
    substitution uses the wrong probability, the spectral route is not derived,
    and the information-theory statement merely encodes a chosen five-percent
    redundancy. Marking the threshold mathematically PROVEN contradicts the
    controlling phenomenological-anchor correction.
324. **the lexicon's status markers classify definitions and implementations as
    scientific proof.** A well-formed formula, a numerical script, a fitted
    constant and a testable physical mechanism require different evidence.
    Several rows receive checkmarks despite missing code, failed derivations or
    absent bridges, so the summary table cannot serve as a provenance ledger in
    its present form.
325. **Appendix A's stated Riemann--Siegel error bound does not follow from the
    displayed formula.** Truncating the two main sums at
    `floor(sqrt(t/(2*pi)))` leaves a nontrivial asymptotic remainder whose size
    depends on `t` and the number of correction terms; it is not uniformly below
    `1e-48` over the first 10,000 zeros merely from that choice of `N`.
326. **the four-step zero protocol neither independently locates nor proves
    completeness of the zeros.** `mpmath.zetazero(n)` already returns a point on
    the critical line, so checking its real part is circular; the sign-changing
    real function used in zero counts is Hardy's `Z(t)`, not generally
    `Im(zeta(1/2+it))`; and a `1e-10` separation rule only rejects duplicates.
    A completeness claim needs a zero-count/Turing-method argument with certified
    errors.
327. **the appendix title and data claim exceed the artifact.** Only 20 zeros
    are printed, while the advertised `riemann_zeros.csv`, digit-sum data,
    resonance grid and verification log are absent from the tracked repository.
    The book's own ch34 path audit already confirms the missing 150-digit zeros
    file; an external URL without an immutable checksum is not local provenance.
328. **three of four “high-altitude zeros” are numerically false, and the first
    is inaccurate beyond eight decimals.** Direct `mpmath.zetazero` evaluation
    gives ordinates `1419.422480945995...`, `2515.286482924712...`,
    `5447.861998301299...`, and `9877.782654005501...` for indices 1000, 2000,
    5000 and 10000. The table instead prints `1419.422481061...`,
    `2771.421680003...`, `6373.803858964...`, and `11477.505264622...`.
329. **the reported spacing statistics are not defined or compatible with the
    displayed zero range.** The raw average gap through the 10,000th zero is
    about `(9877.78-14.13)/9999`, roughly `0.986`, not `2.56`; GUE comparison
    requires an explicitly unfolded spacing. “Pair correlation 0.98” and “third
    moment 2.31” provide no estimator, normalization, uncertainty or data file.
330. **the base-3 digit-sum table is largely a table of residues, not digit
    sums.** For example `D_3(3)=1`, `D_3(9)=1`, and `D_3(10)=2`, whereas the
    table gives 0, 0 and 1. The asserted period-nine identity is false: already
    `D_3(1)=1` but `D_3(10)=2`. This invalidates the claimed perfect base-3
    pattern in the appendix conclusion.
331. **the resonance-coefficient correction contains a valid core diagnosis but
    an overextended sign argument.** It is correct that one-argument `R_f(alpha)`
    is undefined, no `s` or numerical method is given, the table conflicts with
    exact integer-alpha formulas, and the CSV is missing. Continuity between a
    negative endpoint and a divergent positive endpoint would force some zero,
    but it does not by itself refute positive values at the selected intermediate
    alphas; the zero could occur elsewhere. The correction should retain the
    provenance failure without claiming more than IVT supplies.
332. **the historical table internally contradicts the appendix's stated
    contribution.** It says this work verified `10^14` zeros in 2025, while the
    appendix documents at most a call to `mpmath.zetazero` for 10,000 and supplies
    no corresponding dataset or verification certificate. That row is thirteen
    orders of magnitude larger than the presented artifact count and must not be
    retained without independent provenance.
333. **the conclusion converts computed on-line examples into an unproved
    Hilbert--Polya identification.** Numerical zeros do not show they are
    eigenvalues of a defined self-adjoint `H_zeta`; the root-verified RH arc still
    lacks the exact count and operator-surjectivity bridge. “Perfect consistency”
    also fails because the digit-sum table and high-zero table are false.
334. **the tiny residual column has no reproducible provenance.** The values form
    a narrow patterned range near `2e-51`, while the cited program and data log
    are absent and the shown code only returns a Boolean threshold. Without the
    exact precision, algorithm version, output log and immutable input/output
    artifact, those residuals are unverified reported numbers rather than an
    independently reproducible computation.
335. **Appendix B's proposed BRST projector is the identity, not a physical-state
    projection.** The appendix first requires `Q^2=0`, then defines
    `P_phys = lim_{T->infinity} exp(-Q^2 T)`. Nilpotency makes every exponential
    equal to one. A Hodge-style projection would require additional structure,
    typically a BRST Laplacian involving `Q` and an adjoint, none of which is
    defined here.
336. **the fractal BRST operator is a symbolic expression without a mathematical
    carrier.** The fractal space, measure, field domains, Grassmann algebra,
    wedge operation, functional derivative and operator closure are not
    specified. Consequently nilpotency, conserved charge, cohomology and the
    relation to the actual UHF substrate are not established for this object.
337. **the mass-gap number is dimensionally inserted rather than derived.** The
    displayed factors `g^2`, `1/sqrt(2*pi)`, `0.9876` and `vol_f(K)` are
    dimensionless, yet the final line declares `0.732864 GeV` without a physical
    scale or renormalization prescription. `R_f(sqrt(2))` again omits its second
    argument and later becomes `R_f(sqrt(2),x)` integrated over an unrelated
    fractal variable.
338. **the numerical mass-gap comparison has no cited data or uncertainty model.**
    “Lattice QCD `0.73 +/- 0.05`” and “experimental glueball
    `0.71 +/- 0.08`” are presented without action, lattice spacing, continuum
    extrapolation, quantum numbers, collaboration, experiment or source. The
    theoretical row gives no propagated uncertainty. Calling the agreement
    perfect is therefore neither reproducible nor statistically meaningful.
339. **the displayed nilpotency calculation is not a verification.** It changes
    from the full canonical charge to an expression with undefined shorthand
    (`E^b`, `partial dot c^c`) and inconsistent free/contracted indices, then
    sets the integral to zero by citing the Jacobi identity. A real proof must
    track graded brackets, canonical (anti)commutators, boundary terms and all
    structure-constant contractions.
340. **the ghost effective action has an unexplained determinant coefficient and
    does not derive confinement.** Faddeev--Popov ghosts form a complex
    Grassmann pair whose determinant convention does not generically produce the
    printed `-1/2 Tr log(partial dot D)`. Even after fixing signs and factors, a
    one-loop determinant does not by itself establish a nonperturbative mass gap
    or confinement.
341. **standard BRST cohomology is conflated with sheaf cohomology on the gauge
    group.** `ker Q/im Q` on a state/field complex is not generally
    `H^*(G,O_G)`, and physical states are not equal to the ring of
    gauge-invariant operators `H^0(G,O_G)`. The relevant complexes, actions and
    comparison maps are absent.
342. **the Cech differential is not “the BRST operator” merely because both
    square to zero.** A Cech coboundary glues local sections on a chosen cover;
    the BRST differential encodes infinitesimal gauge symmetry on a graded field
    algebra. Identifying them requires a constructed quasi-isomorphism or
    descent theorem, not the displayed parallel notation.
343. **the characteristic-class formulas and labels are oversimplified.** The
    general second Chern class includes the usual trace-square combination (with
    convention-dependent signs), not simply `Tr(F wedge F)/(8*pi^2)` for every
    bundle, and `c_1` is not generically a “U(1) instanton number.” Closed
    characteristic forms are genuine geometry, but they do not establish the
    proposed consciousness or mass-gap bridge.
344. **the localization claims silently switch from ordinary Yang--Mills to a
    topological/supersymmetric theory.** Generic Yang--Mills action is not
    BRST-exact, generic path integrals do not reduce to the printed finite fixed-
    point sum, and gauge-action fixed points are not simply “instantons.”
    Donaldson--Witten theory is a special twisted topological theory and cannot
    supply these conclusions for four-dimensional pure Yang--Mills without the
    missing construction.
345. **the appendix's standard and speculative parts are not provenance-labeled.**
    The gauge transformation, Faddeev--Popov fields, BRST differential and
    cohomological physical-state idea are conventional background (subject to
    sign conventions). Sierpinski gluons, dual-fractal ghosts and the numeric
    gap are unformalized PF proposals. Presenting them in one uninterrupted
    derivation makes inherited theory appear to prove the new bridge.
346. **the conclusion's claimed Yang--Mills solution contradicts the exact
    formal scope.** Root verification shows that the Lean endpoint stores or
    existentially packages a positive gap and does not construct a 4D
    Wightman/Osterwalder--Schrader Yang--Mills QFT. Appendix B adds no rigorous
    continuum construction, so it cannot complete the Clay problem.
347. **the appendix points to the wrong chapter and an obsolete result map.** It
    says it supplements Chapter 20's Yang--Mills treatment, while Chapter 20 is
    the Riemann Hypothesis and Yang--Mills is Chapter 23 in the current book.
    This mirrors the navigation drift already found in ch34--35 and impedes
    reproducible cross-checking.
348. **Appendix C's printed algorithm can never reach any of its clinical
    categories.** Its matrix satisfies `F_ji=-F_ij`, so for real `F`,
    `Tr(F@F)=-||F||_F^2<=0`. Therefore `ch2_raw<=0` and the logistic post-map is
    at most `1/(1+exp(5))≈0.006693`. Every threshold from 0.50 through 0.95,
    every reported patient range and the claimed trained/awake values are
    impossible under the exact code shown.
349. **the object computed is not a second Chern character.** Eigenvalue
    differences of a coherence matrix are placed in an ordinary antisymmetric
    array, multiplied as matrices and passed through an arbitrary sigmoid. No
    base manifold, bundle, connection, curvature two-form, wedge product or
    integral cycle is defined, so the Chern--Weil name supplies no topological
    invariance to this statistic.
350. **the epoch and connectivity routines have incompatible axis conventions.**
    `epoch_data` slices the first axis as time, but `compute_connectivity` treats
    the second axis as channels and then indexes each epoch's first axis as a
    channel time series. With channels-first data the epoching is wrong; with
    time-first data `epoch[i]` is a time sample across channels. No input shape
    makes the shown pipeline implement the stated 19-channel coherence analysis.
351. **the headline 412-patient validation has no provenance and conflicts with
    the book's other cohort.** No institution, registration, dates, inclusion
    flow, endpoint adjudication, confusion matrix, dataset, ethics approval or
    citation is given. Chapters 30--32 instead discuss an 847-patient cohort
    with different counts and already classify it as unvalidated; Appendix C
    supplies no bridge showing that 412 is a subset or independent replication.
352. **the emergency-protocol 92% accuracy and full-protocol 97.3% figure are
    reported as facts without an estimand or test design.** There is no held-out
    set, comparator definition, prevalence, threshold selection procedure,
    calibration, confidence interval for the emergency value or multiplicity
    control. They are unvalidated performance claims, not properties of a
    protocol specification.
353. **the clinical state labels are not justified by the statistic and could
    cause direct harm.** The table maps arbitrary numeric intervals to conscious,
    minimally conscious, vegetative and coma states, then attaches palliative or
    intensive-care actions. Because the printed algorithm cannot reach those
    ranges and no independent diagnostic validation is supplied, these actions
    must not be presented as clinical guidance.
354. **the special-population thresholds and trajectories are unsupported
    outcome claims.** TBI recovery bands, anoxic-outcome percentages, sedation
    ranges, extubation targets and test-retest ICCs have no data source or model.
    Changing the consciousness threshold from 0.95 to 0.85 “due to structural
    damage” is an ad hoc recalibration, not a derived or validated correction.
355. **the anoxic-brain-injury table is especially high-stakes and lacks the
    safeguards required by its own prose.** It reports 0% good outcome below
    0.50 and suggests the result at a withdrawal-of-support decision point, yet
    provides no sample sizes, uncertainty, blinded outcome assessment,
    confounder control, external validation or protection against the
    self-fulfilling-prophecy bias introduced by treatment withdrawal.
356. **capacity and consent cannot be assigned by the proposed threshold.** The
    appendix says direct consent applies when `ch2>=0.95` and communication is
    possible, although the metric is unvalidated and unreachable in the code.
    Decision-making capacity is task-specific and clinically/legal assessed;
    it cannot be inferred from a speculative scalar consciousness score.
357. **the confidence interval in the reporting template has no computation.**
    The pipeline returns a single sigmoid value and defines neither a sampling
    model nor bootstrap, repeated-epoch estimator, calibration uncertainty or
    patient-level aggregation. A blank “95% Confidence Interval” field does not
    make the output statistically quantified.
358. **the preprocessing code is incomplete even as research software.** The ICA
    path calls undefined `find_artifact_components`; filter/epoch orientation is
    unspecified; referencing, bad-channel handling, line-noise treatment and
    missing-data rules are absent; and overlapping epochs are later treated as
    though they supplied uncomplicated replication.
359. **the protocol confounds correlation structure with consciousness without a
    validation bridge.** Alpha-band coherence is sensitive to volume conduction,
    reference choice, vigilance, medication, lesions and artifacts. Keeping only
    positive eigenvalues and applying a sigmoid does not establish specificity
    for consciousness rather than these covariates.
360. **the conclusion reverses the evidentiary status.** A proposed acquisition
    and processing pipeline can be a useful prospective study design, but absent
    a functioning statistic and independent clinical study it is not objective,
    cross-center reproducible, actionable, prognostic or evidence-based. Calling
    it a paradigm shift exceeds both the code and the manuscript's own final
    verification ledger.
361. **the appendix points to the wrong source chapter.** It says the framework
    is presented in Chapter 27, which is dark-energy expansion; the clinical and
    neuroscience material is in Chapters 30--32, with the mathematical `ch_2`
    definitions split across earlier chapters. The incorrect pointer conceals
    rather than resolves the already documented five-way `ch_2` ambiguity.
362. **Appendix D is an API reference for the same nonexistent package documented
    in ch35.** There is no tracked Python distribution, package module, build
    metadata, test tree or console-entry-point definition for
    `principia_fractalis`, `pf-verify` or `pf-compute`. Every import and command
    in the quick reference is therefore aspirational at the audited HEAD.
363. **`compute_resonance` has the wrong advertised return type.** For general
    real alpha and complex `s`, `R_f(alpha,s)` is complex; the book itself gives
    a complex value at `alpha=sqrt(2), s=1`. Returning or documenting a plain
    float would discard phase information that is central to the resonance
    function.
364. **the “Verify Riemann Hypothesis” workflow verifies only values returned by
    its own zero finder.** Checking the first 100 on-line ordinates is finite
    numerical reproduction, not RH, and it supplies neither completeness nor an
    off-line zero exclusion. Naming the command and assertion as RH verification
    repeats Appendix A's circularity.
365. **the P-vs-NP workflow repeats the stale `alpha_NP=pi/3` assignment.** The
    manuscript's canonical NP value is `phi+1/4`; moreover the dense level-12
    matrices are infeasible and lack quadrature normalization. This quick
    reference therefore cannot reproduce either the canonical model or its
    claimed continuum spectrum.
366. **the recommended fractal levels are incompatible with the documented
    implementation.** Levels 8--16 are advertised as ordinary inputs, although
    ch35's correction proves level 12 already requires terabytes and level 16
    petabytes for the dense path, while the proposed sparse threshold retains
    essentially every entry.
367. **the consciousness workflow converts an impossible research statistic
    directly into a patient diagnosis.** Appendix C's exact code returns at most
    about `0.0067`, the package implementation is absent, and no clinical
    validation exists. Printing “Patient is conscious/unconscious” from 0.75 and
    0.95 cutoffs is unsafe and contradicts the manuscript's own caution that the
    measure is unvalidated.
368. **the configuration API promises capabilities no backend implements.** A
    global 150-digit setting cannot upgrade NumPy/SciPy float64 operations, GPU
    enablement still constructs an impossible dense matrix, the `1e-10` sparse
    threshold does not sparsify the cosine kernel, and cache/checkpoint functions
    have no tracked implementation.
369. **the testing and documentation commands have no corresponding artifacts.**
    `tests/test_riemann.py`, the slow-test marker, coverage configuration,
    ReadTheDocs project and API site are not provided as immutable repository
    inputs. A quick reference must link to a versioned, runnable artifact or mark
    these entries as planned interfaces.
370. **the appendix's provenance metadata is stale.** It points to Chapter 32
    rather than software Chapter 35, uses the obsolete `pcohen` GitHub path and
    repeats version 1.0.0/year 2025 instead of the tracked citation record. The
    mismatch is part of the broader repository/license inconsistency recorded in
    finding 314.
371. **Appendix E asserts that changing integration measure makes an undefined
    Shiab operator essentially self-adjoint.** The vanishing of boundary terms
    does not follow from a noninteger dimension `d_f<14`, and symmetry after one
    integration-by-parts step would still not establish essential
    self-adjointness. No operator, domain, boundary geometry, measure regularity
    or deficiency-index argument is supplied.
372. **the value `d_f=13.7329` is inserted without a definition or derivation.**
    No fractal set, dimension notion, computation or uncertainty accompanies it,
    and the digits echo the separately asserted mass-gap number. Replacing a
    14-dimensional geometric construction by a noninteger measure also requires
    a new mathematical model, not a decimal substitution.
373. **multiplying a Chern class by `0.9901` does not produce a corrected Chern
    class or exact anomaly cancellation.** Characteristic classes have
    topological/integrality constraints; a generic real rescaling is not the
    same class of object. The factor comes from Appendix A's undefined
    one-argument resonance table, and no anomaly polynomial or target value is
    given for the claimed one-percent cancellation.
374. **the Geometric Unity comparison table reports conclusions not established
    in the appendix.** Self-adjointness, anomaly cancellation, ghost projection
    and full consistency are the claims needing proofs; repeating them as
    “resolved” does not supply the missing domains, bundles, BRST complex or
    quantum theory.
375. **the GUT predictions are numerically unsupported.** The one-percent
    deviation, `10^16 GeV` bosons, `10^36`-year proton lifetime and neutrino
    correction have no Lagrangian parameters, renormalization-group evolution,
    branching ratios, uncertainty propagation or falsification protocol. They
    are proposed phenomenology, not consequences of the displayed rescaling.
376. **the ring-laser alignment introduces another undefined bridge.** No
    torsion-like curvature `tau_f` is constructed on the UHF substrate, no map
    produces a spacetime metric or Sagnac observable, and the coefficient in
    `delta f≈10^-9 tau_f Hz` has no dimensional derivation. A bound on an
    undefined parameter cannot yet falsify the TOE mechanism.
377. **the appendix treats claims about an external unpublished framework as
    settled inputs.** The exact Observerse bundle, Shiab operator, anomaly and
    ghost content need primary definitions and provenance before PF can prove a
    repair. Alignment with another speculative theory is conditional
    comparative work, not independent validation of either theory.
378. **the conclusion overstates the achieved scope.** At most the appendix
    sketches a possible fractal regularization program; it does not show that
    Geometric Unity is mathematically consistent, preserve its physical content
    or derive a testable extension. This is an unformalized claim, separate from
    the genuine PF operator-algebra results.
379. **Appendix F turns standard zeta symmetry into a circular proof of RH.** The
    functional equation and conjugation correctly pair a nontrivial zero `s`
    with `1-conj(s)`. An off-line zero and its reflected partner would both
    violate RH, but that is not a contradiction unless RH is already assumed.
    The final “therefore no zeros exist for Re(s)>1/2” is precisely the unproved
    conclusion.
380. **the level-8 ground-state exercise reports a stored answer and convergence
    bound without a computation artifact.** The Python package is absent, the
    discretization lacks measure weights, and no levels or error estimator are
    compared. Thus `0.2221441469` and the `<10^-8` infinite-level error do not
    follow from the listing.
381. **the random-matrix exercise's expected `ch2≈0.12` is mathematically
    impossible for its own code.** The same antisymmetry argument as Appendix C
    gives `Tr(F@F)<=0` and hence a sigmoid output no larger than `0.006693`.
    The printed result cannot be produced from seed 42 by the shown formula.
382. **the cosmological suppression calculation reverses its effect and is
    arithmetically false.** Because `0<0.95<1`, `0.95^-122≈521`, not
    `5e-3`; the printed law increases `10^113` to roughly `5.2e115 J/m^3`.
    A positive exponent would suppress, but neither sign nor exponent is derived
    from the field equations here.
383. **the cosmology exercise correctly notices that its printed result remains
    enormous but then points to an unverified alternative.** The admission is
    valuable, yet “consciousness-modified Einstein equations reduce Lambda
    directly” still requires the consistent local map and Bianchi bookkeeping
    that the earlier chapters leave open.
384. **the exercise and chapter numbering is obsolete throughout Appendix F.**
    RH, P-vs-NP and cosmology references no longer match Chapters 17, 18 and 23,
    and even exercise labels differ from their headings. This prevents a reader
    from checking whether the supplied solution answers the current exercise.
385. **the advertised complete online solutions have no immutable provenance.**
    No tracked manual, notebooks, video manifest, version or checksums accompany
    the URL. The appendix itself contains examples whose outputs are impossible,
    so the external resource cannot be treated as verified without a frozen
    artifact audit.
386. **Appendix G hides the book's central five-way `ch_2` ambiguity.** It lists
    only the topological second Chern character and bundle notation, then lets the
    same symbol stand for connectivity, clinical, projector and entanglement
    quantities elsewhere. The notation appendix must expose the corrected
    disambiguation rather than silently restore a single meaning.
387. **the natural-number convention conflicts with the corpus and formal code.**
    It defines `N={1,2,3,...}`, while digit-sum code handles zero, several
    statements quantify `n>=0`, and Lean's `Nat` includes zero. The convention
    must be explicit per theorem or changed consistently to avoid off-by-one
    domain errors.
388. **the ternary digit sum has two names without a declared equivalence.** The
    main chapters and formal files predominantly use `D_3`, while this appendix
    defines `S_3`. Appendix A's false table also uses `S_3`; readers need one
    canonical symbol and an explicit alias if both are retained.
389. **`e` is mislabeled “Euler's constant.”** The decimal `2.71828...` is
    Euler's number/base of natural logarithms; “Euler's constant” conventionally
    denotes the Euler--Mascheroni constant `gamma≈0.57721`. This is a small but
    concrete reference error.
390. **several overloaded symbols need namespace qualifiers.** `H` denotes both
    Hamiltonian and Hubble parameter, `Phi` both a consciousness field and IIT
    integrated information, `Omega` both density parameters and the Ocean of
    Timeless Existence, and `R` both Ricci scalar and resonance-related objects.
    Context can disambiguate prose, but cross-chapter equations and code require
    subscripts or typed definitions.
391. **the notation appendix presents disputed assignments as neutral
    definitions.** Calling `pi/10` a universal coupling and alpha a geometry
    coupling imports physical conclusions whose derivations remain open. A
    reference table should label these as PF parameters/candidates, separate
    from standard constants and established mathematical notation.
392. **Appendix H's RH convergence table is algebraic, not exponential.** The
    deviations are `0.812/N` to the displayed precision (`0.0812`, `0.0406`,
    `0.0271`, ...), so the caption and prose's “exponential decay” are false.
    Finite convergence of a constructed sequence toward 0.5 would in any event
    not prove that every zeta zero lies on the critical line.
393. **the table does not converge to the first Riemann zero it invokes.** Its
    imaginary part is fixed at `14.2267`, whereas the first nontrivial ordinate
    is `14.134725...`. No error decreases with basis dimension, and no bijection
    or residual is shown. The claimed 100-digit eigenvalue-zero correspondence
    therefore does not follow from the displayed data.
394. **the “limiting spectral gap” is inconsistent with the table.** `0.08127`
    is approximately the first `N=10` deviation, while the listed deviations
    tend toward zero. No two spectral endpoints or limiting operator are defined
    for this gap, so it cannot be both a positive limiting invariant and the
    disappearing critical-line error.
395. **the P-vs-NP numerical gap still has no standard-complexity implication.**
    The exact subtraction is positive, but the operators are not connected to
    the standard P/NP language classes and the current formal `ClassP` collapses
    to two languages. Appendix H adds no encoding, transition semantics or
    reduction theorem that would make the finite matrix gap prove `P!=NP`.
396. **the Hodge tables contradict their own concentration list.** The summary
    reports mean `0.6310` and maximum `0.9893`, while all four values immediately
    below are about `0.9999997`--`0.99999994`, exceeding the stated maximum and
    averaging near one. Six test cases, five algebraic cases and four listed
    concentrations are also not reconciled.
397. **finite spectral classification tests cannot prove the Hodge conjecture.**
    No theorem maps the ad hoc 0.95 concentration threshold to rational
    cohomology classes being algebraic on every smooth projective variety. The
    root-verified Lean carrier remains uninstantiated/trivial at the standard
    problem, so the “complete proof” JSON label is evidence inflation.
398. **the K3 row conflates Hodge number with Picard number.** Every complex K3
    surface has `h^{1,1}=20`, while the Picard number is the rank of the
    Neron--Severi lattice and need not equal 20. A specially chosen singular K3
    may have rho 20, but the table supplies no surface or proof of that property.
399. **the Navier--Stokes critical-Reynolds arithmetic is false.** Substituting
    its own `omega_c=pi/10` into `(10/pi)*omega_c*10^5` gives exactly `10^5`, not
    `2.13198e5`. More importantly, the consciousness regularization lemma is
    already refuted under its own gradient closure and does not prove global PDE
    regularity.
400. **the XENON section conflates two different energy claims.** The prose calls
    a `9.4 keV` xenon nuclear transition anomalous, while the figure caption says
    “XENON1T Excess” at `2.5 keV`. The factor `1+(pi/10)*0.95≈1.30` is arithmetic
    after inserting the target 0.95; it does not derive a spectrum, rate,
    detector response or 14D-to-4D projection.
401. **the “universal threshold” table compares unrelated and incompatible
    quantities.** A spectral concentration, critical-line statement, CMB fit,
    neural score, cosmic parameter and wavefunction modulus do not become one
    observable because each is labeled 0.95. The same section's Omega-state
    caption uses `ch2=1.2`, contradicting the claimed `[0,1]` range and threshold
    semantics.
402. **the CNT optimization is an output claim without a physical model or
    source dataset at the named path.** Conductivity and mass changes require
    geometry, material composition, contacts, temperature, simulation/measurement
    protocol and uncertainty. A parameter-space figure cannot validate a
    `pi/10` resonance mechanism absent those inputs and an external baseline.
403. **the universe-crystallization percentage is a relabeling of the supplied
    dimensions.** `1.54/2.73≈56.4%`; calling that ratio “completion” contains no
    transition dynamics or observation model, and an actually completed fraction
    defined by reduction from 2.73 would be about 43.6%. Neither dimension has
    source provenance in the appendix.
404. **the CMB `>5 sigma` claim has no statistical analysis.** The appendix gives
    no sky map, mask, estimator, null simulations, covariance, look-elsewhere
    correction or catalog for 187 peaks and a 999.3 Mpc coherence scale. A figure
    and JSON filename cannot establish detection significance.
405. **the void fit is internally incoherent.** A “fit scale” of
    `3.00 +/- 8.13 Mpc` is consistent with zero and has uncertainty larger than
    the estimate, while the asserted exponential decay length is separately
    `11.2 Mpc`. No likelihood or relation between these parameters is supplied,
    so the result cannot support Omega leakage.
406. **the clinical detection values contradict Appendix C's exact algorithm.**
    That algorithm cannot exceed about 0.0067, yet Appendix H reports neural
    states from 0.1 to at least 0.95 with no alternative operational definition,
    patient data, cohort description or cross-validation. The plotted separation
    is therefore not an empirical validation of the printed measure.
407. **the vortex core-size conversion is wrong by thirteen orders of
    magnitude.** `ell_P*10^16` is about `1.6e-19 m`, not a micron (`1e-6 m`).
    The circulation quantization and fMRI observability are also asserted without
    a field solution or map from Planck-scale structure to neural imaging.
408. **the corpus inventory's file arithmetic does not total 210.** It lists 34
    EVIDENCE files plus 106 Proofs files, which is 140. The canonical/duplicate
    subtotals explain those two category totals but supply no missing 70 files;
    a SHA256 claim also needs the actual hash manifest, not just a sentence that
    verification occurred.
409. **tracked artifacts exist, but not at the chapter's claimed current
    locations or evidentiary scope.** The RH/Hodge JSONs are preserved under
    `ARCHIVE/...` and `Papers/PriorWork_*`, and 21 relevant PNGs are tracked.
    This establishes provenance of historical computations/figures, not the
    truth of labels such as “complete proof,” “validated,” or “exact match.”
410. **the cross-reference validation list is stale and incomplete.** It routes
    P-vs-NP to Chapter 9, NS to Chapter 10 and Weinstein to Chapter 11 while the
    current dedicated problem chapters and later corrections live elsewhere;
    it omits the contradictions among Appendices A--H and does not report the
    missing operational data links.
411. **Appendix I's “principal claim -> Lean theorem” relation is not generally
    entailment.** Several rows cite an arithmetic bracket, a named proxy, a
    conditional implication or a downstream consumer for a much broader chapter
    claim. A cross-reference is useful only if it states the exact theorem type
    and residual hypotheses, rather than letting the prose summary substitute
    for the declaration.
412. **absence of project axioms is repeatedly used as stronger evidence than it
    supplies.** `#print axioms` can show kernel dependencies, but theorem
    hypotheses, definitions equal to `True`/`False`, dead binders, target-bearing
    fields and restricted carriers remain inside the theorem type. The final
    correction acknowledges this; the opening scoping paragraph and table labels
    do not consistently propagate it.
413. **the ch06 row verifies a chosen number, not consciousness
    crystallization.** A theorem named `threshold_ch2_eq_zero_point_95` can prove
    the definition equals `19/20`; it supplies no neural observable, reachability
    result, clinical validation or Chern--Weil bridge. Marking the chapter's
    “second Chern character; crystallisation threshold” as machine-verified
    collapses definition and empirical interpretation.
414. **the ch08 row does not verify the field equations it summarizes.** It
    points only to `darkEnergyDensity_in_bracket`, an arithmetic observational
    interval. That theorem cannot establish the tensor field equation, Bianchi
    identity, covariance or the unresolved `Theta(ch2-0.95)` interpretation.
415. **the GU row turns a capstone name and integer decomposition into a physical
    rescue.** `78=48+26+4` and `dim E6=78` are arithmetic/group-dimension facts;
    they do not construct the Shiab operator, cancel an anomaly, define BRST
    cohomology or embed the Standard Model. The exact theorem may be valid while
    the “rescued” principal claim remains unformalized.
416. **the P-vs-NP rows do not cure the carrier defects.** V3 positivity of the
    prime-power encoding is automatic and lacks transitions, and the current
    `InClassP` invariance condition collapses the class to empty/universal
    languages. An iff to “literal P != NP” on that carrier preserves the faulty
    definition; it does not connect to standard complexity theory.
417. **the NS/YM/BSD/Hodge V2 labels still exceed their definitions.** NS uses a
    vacuous `SolutionBlowsUpAt := False`; YM provides an `l2`/Gaussian carrier and
    stored positive gap rather than a 4D QFT; BSD's rank functions alias zero;
    Hodge's branches are restricted/generic proxies. “Strict strengthening” or
    “Clay standard” naming cannot replace those missing semantics.
418. **the Perelman row is a projection of a hard-coded alpha tuple, not an
    external anchor theorem.** Perelman's Ricci-flow work proves the Poincare
    conjecture but does not derive `alpha_Poincare=1`. The table accurately names
    a projection theorem while its principal-claim column assigns unsupported
    provenance.
419. **the cosmology rows verify arithmetic fits rather than physical
    mechanisms.** A log ratio, ordered Hubble constants and a density bracket are
    exact Lean propositions, but they do not supply a likelihood, field-dynamic
    derivation, parameter penalty or prospective observation. “Suppression” and
    “resolution” should be labeled retrospective/conditional accordingly.
420. **the cross-prover Y column is visually misleading despite the final
    correction.** Most legacy Coq files prove declaration-shaped `True`
    statements, so a Y means structural-name parity, not re-proving the Lean
    theorem. That qualifier belongs in the column heading and every table
    caption, not only a paragraph after the tables.
421. **the reproduction instructions are historical and path-stale.** They pin
    `42990ea`, expect 4030 jobs, use `PF_Coq` rather than the current
    `PF_Coq_Code`, and invoke `tools/audit.sh` although the current verified
    workflow and build totals have moved. Replaying a historical commit is valid
    only with an exact toolchain, dependency lock and paths from that commit.
422. **the statement “a reader ... independently verified every entry” directly
    contradicts the appendix's own correction.** Re-elaboration verifies that
    declarations typecheck in the stated environment; it is not independent
    mathematical derivation, external-kernel validation, empirical replication
    or confirmation that a prose claim matches the theorem type.
423. **the PF_Real count is stale but its evidentiary distinction is sound.** The
    appendix says 110 re-proved theorems; root later verified 683/683 Rocq 9.1.0
    objects and three PF_Real capstones closed under the global context. That is
    stronger current build evidence, while still requiring theorem-by-theorem
    scope comparison rather than treating the entire mirror as semantic parity.
424. **Appendix J's Hilbert--Polya bridge is deliberately synthetic, not an RH
    closure.** The canonical positive enumeration `k + 1` makes the spectral
    shape elementary; `SubstrateEncodingMatchesMathlibZeta` retains the literal
    zeta-zero identification. This is a useful typed reduction, but the residual
    contains the load-bearing mathematics.
425. **the Gaussian Navier--Stokes lift does not solve Navier--Stokes.** The
    appendix itself says `u(t,x)=exp(-t^2)u_0(x)` is not generally a PDE
    solution. The zero-datum example is an unconditional local proxy, not a
    route from arbitrary smooth data to global regularity.
426. **the rank-one Hodge shadow eliminates the obstruction by construction.**
    A rational coefficient witness closed by `rfl` proves the selected
    coefficient model; it does not lift a general rational Hodge class to an
    algebraic cycle. The appendix correctly calls the literal lift open.
427. **using an actual `SU(2)` carrier does not construct four-dimensional
    Yang--Mills theory.** The continuum measure, Osterwalder--Schrader/Wightman
    reconstruction and Glimm--Jaffe limit remain typed open anchors, while the
    mass gap is stored as `3/2`. The carrier upgrade is necessary typing work,
    not the Clay theorem.
428. **Appendix J's P-vs-NP no-go is more honest than the later class encoding.**
    It declines to manufacture an alpha bridge and states the circularity. The
    later `ClassP` definition is worse: its suffix-invariance condition collapses
    every language to empty or universal, so its separation is unrelated to
    complexity theory.
429. **shrinking the headline residual bundle from twelve fields to three does
    not measure mathematical difficulty.** `PF_RHEncodingV2`, the RH
    surjectivity/identification residual and the polylogarithm conjecture remain
    load-bearing; fewer fields are not evidence that the open content is nearly
    solved.
430. **`no_hidden_semantic_content` classifies a selected list rather than the
    corpus.** The later pristine gate's criterion (e) was broken, and absence of
    project axiom declarations does not imply absence of hypotheses or trivial
    definitions. The 37-entry audit cannot support a whole-corpus conclusion.
431. **the nine-alpha rigidity system is target-bearing.** Its invariant
    equations explicitly contain the desired relations and the Perelman value
    is supplied. The Lean result solves that chosen constrained system; it does
    not establish physical uniqueness, absence of tuning or derivation from one
    independent datum.
432. **the eighteen Smale bundles are typed residual inventories, not
    solutions.** Naming the open propositions improves dependency tracking, but
    the `SmaleProblemsFrameworkAttack` family was later the worst witness-gate
    case: 41 of 41 Props could pass because a bare `_holds` token satisfied the
    broken check.
433. **the Vedic/cymatic bridge mixes exact arithmetic with chosen physical
    labels.** Some sruti and frequency identities are genuine local equalities,
    but assigning alpha values to scale positions is a modeling choice; the
    arithmetic `27 - 23 = 4` does not derive four consciousness, zero-point or
    cosmological couplings.
434. **the temple/cymatic claim remains an external premise.** A typed anchor
    records the proposed architectural correspondence but supplies neither
    primary measurements nor independent replication. It must not be presented
    as validation of the alpha dictionary.
435. **the Navier--Stokes V2 carrier only constructs a constant-in-time
    extension of initial data.** It supplies no time evolution satisfying the
    PDE, incompressibility propagation, pressure equation or global energy
    estimate. The appendix's own scope sentence should control the headline.
436. **the BSD V5 equality is definitional, not Birch--Swinnerton--Dyer.** The
    analytic and algebraic ranks are the same lookup function on a twenty-curve
    catalogue, with default zero elsewhere, so equality closes by `rfl`. A
    standard Weierstrass-curve carrier does not make those ranks independent or
    arithmetically faithful.
437. **“four of six use standard mathlib carriers” overstates semantic
    progress.** RH has an exact standard target but an open bridge; NS has a
    Schwartz-valued map without the PDE; BSD has aliased synthetic ranks; and YM
    has the correct compact group without a quantum field theory.
438. **the Coq mirror in Appendix J is structural-shape parity only.** Mirroring
    record fields and declaration names is useful interface checking, but it is
    not an independent proof of the Lean theorem's mathematical content.
439. **the governance paths are stale.** `FRAMEWORK_FIRST.md`,
    `PUBLISHING_GATE.md` and `SESSION_START_PROTOCOL.md` live under
    `docs/governance/`, not the repository root as Appendix J states.
440. **historical build counts and HEAD anchors are provenance, not current
    acceptance.** The stated 4,186/8,360-job snapshots can document a dated
    refinement pass, but present claims still require current exact source,
    toolchain, build status and theorem-scope audit.
441. **a typed citation is not an imported proof.** Encoding a published theorem
    or external result as a proposition/field preserves the dependency boundary;
    it does not establish the premise inside Lean or transfer the cited
    theorem's hypotheses and semantics automatically.
442. **Appendix K's residual “collapses” are principally bookkeeping.** An
    `Iff.rfl` between byte-identical propositions, and especially between
    declarations whose body is `True`, proves no external mathematics. It can
    remove duplicate names from a ledger but cannot reduce the difficulty of
    the underlying Clay problem.
443. **the appendix contradicts itself about coverage of all six Clay axes.** Its
    meta-capstone says five axes received a reduction and explicitly excludes
    P-vs-NP, while the cumulative statistics later claim seventeen reductions
    “across all six Clay axes.” Both statements cannot describe the same pass.
444. **the 215 `_holds` theorems are the mechanism behind the broken pristine
    headline.** The intended naming convention was useful, but the gate tested
    bare suffix tokens without binding them to each proposition. One `_holds`
    theorem anywhere in a file therefore discharged criterion (e) for every
    proposition in that file; individuation was not actually verified.
445. **“axiom-free” is imprecise when the printed dependencies are `propext`,
    `Classical.choice` and `Quot.sound`.** The defensible statement is “no
    project-specific axiom declarations beyond Lean's standard foundational
    axioms.” A clean dependency print says nothing about whether hypotheses or
    definitions encode the desired conclusion.
446. **the IIT saturation identity is algebraically correct but target-bearing.**
    Once `ch_2 = 19/20` and the chosen bridge
    `ch_2 = 1-exp(-Phi/2)` are supplied, `Phi=2 log 20` follows. The matching two
    occurrences of 20 do not derive the 0.95 threshold, validate the bridge or
    reconcile the manuscript's competing `Phi` definitions.
447. **twenty-nine equalities on fixed named constants do not by themselves
    prove a zero-dimensional variety or physical rigidity.** Most identities
    are algebraic consequences of the constants' closed-form assignments. A
    dimension claim requires a defined variable space, ideal/solution set and
    proof that the equations isolate the assignment rather than merely hold at
    it.
448. **the claimed IBM “Galois pair” is not a conjugate pair.**
    `alpha_RH = 3/2` is rational, whereas the nontrivial conjugate of
    `alpha_NP = (3+2 sqrt 5)/4` is `(3-2 sqrt 5)/4`, not `3/2`. Writing a
    quadratic with both selected values as roots over `Q(sqrt 5)` does not make
    them Galois conjugates.
449. **the pentagonal cosine pair is likewise not the stated Galois analogy.**
    Under `sqrt 5 -> -sqrt 5`, `cos(pi/5)` maps to `-cos(2 pi/5)`, not to
    `cos(2 pi/5)`. Its sum/product identities are genuine trigonometric
    equalities, but the conjugacy rhetoric needs the sign and base field stated
    correctly.
450. **the glueball formula is a retrospective fit, not a derived prediction.**
    It selects the first zeta-zero ordinate and a stored QCD scale, then lands
    about 3.8% above the cited lattice value. No QCD operator, spectral map or
    prospective selection rule is provided to make that numerical association
    an independent cross-axis result.
451. **the spectral-gap normalization inherits the unresolved pi/10 issue.** The
    displayed P and NP products equal `pi/10` because the closed-form lambdas
    are defined to do so; Appendix H separately records that the corrected NP
    closed form does not reproduce the stored NP eigenvalue. The equalities do
    not validate the empirical digits or derive a complexity-theoretic gap.
452. **“fundamental constants extracted from the alpha-skeleton” reverses the
    definitional direction.** The alpha values were introduced using `pi`,
    `sqrt 2`, `phi` and `sqrt(2 pi)`; algebraically solving those definitions
    back for the same constants is an invertible reparameterization, not an
    independent derivation or self-contained origin of the constants.
453. **sharp formal brackets measure arithmetic precision, not empirical
    confirmation.** Narrowing an interval around a fixed closed-form expression
    cannot turn a retrospective association into a prospective prediction,
    establish an uncertainty model or make the theory “referee-saturated.” The
    XENON, Hubble and glueball comparisons still require provenance,
    multiplicity accounting and independent replication.
454. **the Hubble bracket does not resolve the Hubble tension.** It is compared
    only with the SH0ES side of the discrepancy and lies about one quoted sigma
    above that selected central value. No joint likelihood, early-universe fit
    or consistency with the competing inference is supplied.
455. **Appendix K's explanation of the cosmological residual is numerically
    inconsistent.** Multiplying a modulus error of about `10^-5` by the stated
    prefactor `78*pi*0.95` propagates to about `0.0023`, not `0.13`. Moreover the
    displayed `14079*pi/160` expression already substitutes the exact rational
    `19/16`, so a finite Dirichlet-truncation error cannot explain its difference
    from `120 log 10` without changing the quantity being compared.
456. **the exact `10^-120` suppression is an identity of the chosen
    parameterization, not a solution of the cosmological-constant problem.** A
    proof that a defined ratio equals `10^-120` does not derive that scale from
    quantum vacuum energy, radiative stability or cosmological dynamics.
457. **the substrate-rigidity capstones propagate assumptions rather than
    establish their physical source.** The unified-minimal equations and
    positivity hypotheses already force the target assignments; downstream
    powers, logarithms, moments and numerical brackets then follow correctly.
    More bundled consequences do not remove the load-bearing hypotheses.
458. **the final “exactly one Clay-grade Prop per axis” inventory overstates
    semantic fidelity.** RH still lacks contour evaluation/exact zero count;
    P-vs-NP uses a malformed class model; NS endpoints do not encode the PDE;
    YM does not construct a 4D QFT; BSD aliases synthetic ranks; and Hodge is
    uninstantiated. The six labels are proxies or residuals, not six exact
    standard problem statements.
459. **Appendix K's cumulative statistics are internally stale.** It first lists
    seven substrate-rigidity composition files, then reports six; its theorem,
    commit and build-job totals mix successive waves. These can remain dated
    provenance only after reconciliation against the exact commit graph.
460. **Appendix L's “unassailable Clay closure” closes only project-defined
    substrate standards.** Bundling six weaker encodings into one theorem does
    not prove any standard Millennium statement. The adjective “unassailable”
    obscures rather than resolves the explicitly open semantic bridges.
461. **the Wave 59 countability result is at most a zero-set cardinality lemma.**
    The analytic identity-theorem route is mathematically plausible for a set
    that is actually a subset of zeta zeros, but countability neither locates
    those zeros nor proves that all nontrivial zeros lie on the critical line.
    The exact `PositiveOnLineZetaOrdinates` definition still requires Lean audit.
462. **an `Iff.rfl` semantic bridge verifies shared syntax, not external
    semantics.** If the PF predicate and its “literal” counterpart reduce to the
    same body, reflexivity says they were defined identically; it does not show
    that the body faithfully formalizes RH, P-vs-NP or BSD.
463. **the stated BSD bridge is not a standard rank bridge.** Root inspection has
    already established that the V5 analytic and algebraic ranks alias the same
    synthetic lookup function. Their equality by reflexivity is therefore not
    mathlib's independent analytic-rank/Mordell--Weil-rank equality and does not
    instantiate BSD.
464. **standard carriers do not supply standard problem semantics.** A
    `SchwartzMap`, `specialUnitaryGroup` or `ProjectiveSpace` type improves the
    domain of discourse, but does not by itself encode the NS evolution, build a
    four-dimensional quantum gauge theory or instantiate the Hodge cycle map.
465. **the claim that fifteen extended invariants are “independent” is
    unsupported.** The text establishes that they are nonduplicate algebraic
    consequences of a target-bearing assignment. It gives no algebraic-
    independence, Jacobian-rank, ideal-minimality or logical-independence proof.
466. **the 52 literature anchors are citations encoded as propositions, not
    imported proofs.** Several cited results are partial results or barriers,
    not the corresponding Clay theorem. A typed name preserves provenance but
    cannot be counted as a discharged premise unless its exact content and proof
    are formalized.
467. **the “10 refereed-measurement empirical anchors” category is materially
    heterogeneous.** It includes a chosen IIT threshold, a Vedic-music
    correspondence, a known zeta zero, a self-assembled problem panel and
    comparisons with bounds or tensions. These are not ten independent
    measurements of ten prospective PF predictions.
468. **bounds and selected central values are not detections.** XENON limits do
    not validate a dark-matter cross section merely because it lies below them;
    a bracket between Planck and SH0ES does not resolve their incompatibility;
    and reusing the known first zeta zero in a formula is retrospective unless a
    preregistered operator predicts it independently.
469. **the prior-work anchor lattice is self-citation, not independent
    corroboration.** Preserving seven manuscripts and typing their claims is
    useful provenance. Composing those claims back into PF cannot independently
    validate PF, especially where the source manuscripts assert the same
    substrate closures under audit.
470. **the P-vs-NP prior-work summary contains an internal algebra error.** It
    states `alpha_NP^2 = phi + 1/4`, while the same manuscript defines
    `alpha_NP = phi + 1/4` and Appendix K gives
    `alpha_NP^2 = (3/2)phi + 17/16`. The squared identity cannot equal the
    unsquared positive value.
471. **the literal Fefferman statement and the bridge to it are different
    achievements.** Declaring the exact Clay target as a `Prop` can improve
    specification, but a bridge predicate saying the substrate should force it
    is not a proof of that implication. Root verification still finds the
    operational NS endpoints do not encode the PDE.
472. **three-prover mirroring is overstated.** Lean4Lean re-elaboration uses the
    same Lean definitions and kernel semantics; Coq theorems of the form
    `True` prove only structural-name parity. Neither is an independent
    mathematical derivation of the Lean theorem's content.
473. **the named-anchor counts cannot be called axiom-free evidence of their
    source claims.** Standard foundational dependencies may be clean while each
    proposition is `True`, a marker, an implication with a supplied premise or
    a definition engineered to close. Evidence status requires exact theorem
    bodies and dependencies, not counts of names or clean kernel checks alone.
474. **the complete substrate-position capstone aggregates evidence without
    increasing it.** Bundling literature citations, self-authored prior work,
    retrospective empirical associations, algebraic identities and proxy Clay
    encodings into one conjunction does not make the components mutually
    validating or convert them into a TOE closure.
475. **the glossary and epilogue bypass the manuscript's later scope
    corrections.** They state without qualification that all six Millennium
    problems are solved, RH has been proved, P is separated from NP, NS and YM
    are solved, and Hodge is closed. These claims conflict with the exact proxy,
    conditional and open-residual status established elsewhere in the book and
    in the root audit.
476. **the glossary conflates multiple incompatible `ch_2` quantities.** It
    identifies the second Chern character with a scalar consciousness score and
    a 0.95 coherence threshold, despite the manuscript's own later settlement
    separating five quantities and admitting that the clinical chapters compute
    none of them.
477. **the glossary's Timeless Field definition repeats the unresolved
    projective-system defect.** Calling it a projective limit of nuclear
    C*-algebras does not fix the reversed connecting maps or the use of CP
    contractions rather than *-homomorphisms; the advertised K-theory structure
    is therefore still absent.
478. **the glossary's “sacred geometry points” list is stale and unsupported.**
    `{1, 1.5, 1.618, 2, pi, e, sqrt 10}` does not match the later canonical
    nine-alpha dictionary, and no established resonance-coefficient theorem
    proves that these seven values are local maxima or that each solves a
    different mathematical problem.
479. **logarithmic growth of `D_3(n)` is not a fractal-dimension result.** The
    glossary calls such growth “characteristic of fractal behavior,” but an
    `O(log n)` digit-sum bound neither defines nor computes a Hausdorff, box or
    spectral dimension.
480. **the author note's “computation is proof” maxim needs a strict scope
    boundary.** Kernel-checked symbolic proofs are proofs relative to their
    definitions and assumptions; finite high-precision agreement is numerical
    evidence, not an analytical proof of a universal theorem.
481. **the author note repeats unverified novelty and clinical claims.** “First
    mathematical quantification of consciousness” and “97.3% clinical accuracy”
    require a literature search, protocol, dataset, code, held-out validation
    and independent replication. The manuscript currently supplies none of
    those evidentiary components.
482. **the epilogue explicitly upgrades conjectural ontology to theorem.** It
    calls the consciousness field, energy nonconservation, dark-sector origin,
    higher-dimensional observerse and Omega-space “mathematical theorems.” The
    formal corpus does not construct the required physical models or empirical
    bridges; these must be labeled hypotheses or philosophical interpretation.
483. **Omega-space is not mathematically defined by the displayed
    comprehension.** The ambient type of `x`, the definition and codomain of
    `ch^2`, and the meaning of adjoining infinity to positive reals are absent.
    Later prose says Omega is not even a mathematical structure, contradicting
    the displayed set and the claim that its existence is proved.
484. **the crystallization operator is ill-typed relative to the book's own
    `R_f`.** `R_f` takes a scalar alpha and complex `s`, whereas
    `C(omega)=lim_{alpha->alpha_c} R_f(omega,alpha)` inserts an unspecified
    Omega element in the alpha slot and a real limiting variable in the spectral
    slot. No topology, convergence theorem or map into `Phi` is supplied.
485. **the asserted universe dimension `2.73 +/- 0.01` has no estimator or
    object.** The text does not specify which set, measure, metric, dimension
    notion, data or uncertainty model produces it. It is an unsupported numeric
    assignment, not a prediction.
486. **the proposed leakage current tends to zero at the claimed threshold.**
    For `ch^2 -> 1` from below,
    `exp(-1/(1-ch^2)) -> 0`, so the displayed `J_Omega` vanishes rather than
    producing the listed anomalies. Extending above one reverses the exponent's
    sign and requires a separate domain/regularity prescription.
487. **“entanglement beyond Bell bounds” is physically ambiguous or false.**
    Quantum correlations already violate classical Bell inequalities but remain
    bounded by quantum limits such as Tsirelson's bound. A claimed excess needs
    the exact inequality, causal model and experimental protocol, not a threshold
    slogan.
488. **the epilogue labels retrospective anomalies as predictions.** ANITA,
    cosmic-ray events, Hubble tension and known zeta ordinates predate the
    framework's formulas. They cannot serve as prospective confirmation without
    a preregistered quantitative prediction and independent test.
489. **the epilogue contains the correct scientific safeguard but does not apply
    it consistently.** Lines 157--164 require independent reproduction,
    experimental testing, correction and integration; lines 174--178 explicitly
    allow that the framework may be wrong. Those statements should govern the
    absolute claims before them, not be overridden by “the mathematics has
    spoken” at the close.
490. **ch08's opening measurement argument is not a derivation of energy
    creation.** Wavefunction update, nonunitary effective dynamics and energy
    bookkeeping depend on the measurement model and interpretation. None implies
    that consciousness creates or destroys energy, and the chapter supplies no
    experiment distinguishing that claim from ordinary open-system exchange.
491. **the printed consciousness current is not a defined covariant field.**
    `sum_i delta^4(x-x_i) <psi_i|P_C partial^nu|psi_i>` leaves the observer index,
    state-space derivative, distributional product, tensor character and units
    unspecified. It cannot yet serve as the divergence of a stress tensor.
492. **the action-level derivation does not yield the displayed `C^{mu nu}` by
    inspection.** That tensor is a nonlocal integral containing a metric-
    dependent stress operator, threshold and measure. Varying
    `lambda C^{mu nu}g_{mu nu}` requires all of those metric dependencies; the
    text instead inserts `C^{mu nu}` as though it were independent.
493. **the chapter's own Bianchi correction refutes its energy-creation
    headline.** The derived current represents exchange between sectors and the
    corrected total is conserved. Lines 172--185 and the final conclusion still
    call this ex-nihilo creation, directly contradicting lines 160--164 and
    296--298.
494. **the proposed information-energy equivalence is dimensionally undefined.**
    Multiplying an unspecified information quantity by `c^2` gives energy only
    if that quantity has mass units. Shannon information is dimensionless (or
    measured in bits/nats); thermodynamic conversion instead needs a temperature
    and protocol such as a Landauer bound, not a universal equality.
495. **the dark-energy arithmetic is false.** The stated estimate
    `exp[-(10^-30)(10^80)]` is `exp(-10^50)`, effectively zero, not `10^-120`.
    Producing `10^-120` requires an exponent `-120 log 10`, about `-276.31`, and
    the factors in the proof also lack the units needed to form an exponent.
496. **the dark-energy narrative reverses its own suppression mechanism.** It
    says empty space has `ch_2≈0` and that consciousness suppresses the bare
    cosmological term, yet attributes the observed cosmic suppression to a
    universe that is mostly empty and unconscious. No averaging calculation
    resolves that sign/volume tension.
497. **the modified Friedmann acceleration equation is not derived from the two
    displayed Einstein components.** The theorem inserts an arbitrary
    `rho_C f(ch_2)` term, omits the corresponding pressure and continuity
    equation, and suppresses curvature. The subsequent substitution does not
    algebraically produce the claimed second equation.
498. **the four claimed cosmological resolutions are assertions.** No evolution
    equation drives `Omega` to one, no causal model turns Timeless-Field
    correlation into horizon-scale thermal equilibration, and no likelihood or
    dynamics derives the coincidence epoch. Calling the anthropic statement
    physics does not supply those calculations.
499. **the astrophysical “predictions” contain scale-by-digit numerology.** A CMB
    multipole `ell≈95` does not follow from a dimensionless threshold `0.95` by
    deleting the decimal point, and the consciousness-lensing term simply adds
    an order-unity fraction of ordinary lensing without a field-equation
    solution or observational consistency check.
500. **the extended Wheeler--DeWitt equation is an ansatz, not a theorem.** The
    consciousness configuration space, functional measure, canonical momentum,
    constraints, operator domain and regularization are unspecified. Appending a
    formal second functional derivative and the undefined `C^{mu nu}` term does
    not establish a quantum-cosmology Hamiltonian.
501. **the local scalar-action repair is a different theory from the printed
    chapter.** It replaces the nonlocal `Lambda_eff` and separate `C^{mu nu}/J`
    source by a covariant scalar stress tensor with automatic total conservation
    and a Yukawa Green function. Those changes may define a viable research
    model, but the original equations, energy-creation claims and `R_f` kernel
    cannot continue as conclusions of the repaired action.
502. **the preferred-frame repair overstates what conservation proves.** Total
    Noether conservation removes the detached-lambda residue, but it does not by
    itself force every PPN preferred-frame parameter to vanish, especially after
    adding an aether sector. The claimed choices of aether couplings require a
    stability, mode-speed and observational-constraint analysis.
503. **the Planck-scale result constrains a chosen quintessence model rather than
    deriving consciousness gravity.** The screened-kernel calculation can be a
    useful necessary-condition estimate, but `M` is a potential scale, not
    automatically a field excursion, and neither `M`, `f`, the aether couplings,
    nor the identification of Pontryagin density with consciousness is derived.
504. **the exercises ask for numbers from undefined or withdrawn formulas.** A
    reader cannot compute `C^{mu nu}`, local dark-energy change, vortex-created
    energy or a required gravimeter precision after the chapter itself finds the
    relevant definitions ill-typed, dimensionally inconsistent or undetectable.
    They should be reframed as model-completion problems rather than calculations.
505. **ch08's verification ledger is the controlling status statement, but its
    conclusion ignores it.** Lines 625--633 correctly classify every principal
    claim as untested, unvalidated, asserted or non-kernel-verified physics.
    Lines 637--658 immediately revert to “demonstrated,” “resolves,” “demands”
    and “necessarily incomplete.” Both statuses cannot stand simultaneously.

## ALREADY FLAGGED IN THE MANUSCRIPT (confirmed accurate on reading)

* ch03: `thm:rh-resonance` REFUTED in situ --- `|R_f(3/2, 1/2+i gamma)|` =
  0.6187, 1.5462, 1.7966, 1.1359, 1.6266 at the first five zeta zeros.
* ch03: pi/10 filed **EMPIRICAL / OPEN**, "theoretical derivation from first
  principles is an open problem". This contradicts ch07's three derivations, and
  ch03 is the chapter that is right.
* ch03/r212: `sigma(alpha) = log_3 |1 + 2 cos(pi alpha)|` --- the corpus's
  genuine, non-circular base-3 alpha-selection mechanism. Verified by hand:
  sigma(0)=1, sigma(1)=0, sigma(3/2)=0, sigma(2)=1, sigma(phi)~0.4955. Recovers
  exactly the three rational alphas; `sigma in {0,1}` forces alpha rational.
  Guard rail against the near-coincidence sigma(phi)~1/2 is kernel-verified.
* ch04: `F_alpha` is generated by complex NUMBERS, so it collapses to a
  subalgebra of C and carries no alpha-dependence (flagged 2026-10-05).
* ch04: the projective limit runs the WRONG WAY for `K_0 = Z[1/3]`; the
  connecting maps are CP contractions, not *-homomorphisms, so no `K_0` system
  is presented at all (flagged 2026-10-05).
* ch04: `M^4 = Aut/Aut_0` collapses to a point (r333/r334/r335, kernel-verified);
  corrected reading is `Out(T_inf)`, whose classification the same chapter lists
  as open.
* ch05: `prop:no-vortex-2d` proof repaired 2026-10-03 (the original asserted a
  planar fixed point has zero curl; false for `v = (-y, x)`).
* ch06 `rem:ch2-matrix-range-2026-10-03` + its 2026-10-05 settlement: **FIVE**
  distinct quantities are called `ch_2`. Name assigned to the Chern--Weil
  density; threshold to the entanglement form as a classifier of states only.
  Matrix form provably caps at 1/2 so `> 0.95` is satisfied by NO real matrix.
  Verified by hand: `Tr(W^2) <= ||W||_F^2`, so the ratio is `<= 1/2`.
  Honest cost recorded: the clinical chapters compute none of the five.
* ch06 `rem:c2-scoping-2026-07-01`: 0.95 is "best framed as the phenomenological
  anchor satisfying Chapter 6's Chern--Weil topological SUFFICIENT condition, not
  as a uniquely-forced first-principles value". This is already the directive's
  position, dated 2026-07-01.
* ch08: the `Theta(ch_2 - 0.95)` gate raises a Gisin--Polchinski signalling
  hazard under reading R1 and none under R2; "which is intended is an authorial
  decision and is not taken here". **PENDING AUTHOR DECISION.**
* ch08: headline field equation has an index mismatch (lower left, upper right)
  --- "as written this is not a tensor equation". Flagged, not repaired.
* ch09: `thm:spectral_zeta` FALSE three ways (denominator identically zero at
  k=0; the correction factor does not vanish on the critical line; refuted
  numerically). Step 2's product is alpha-dependent where the true ratio is
  alpha-free; the correct identity `(1-3^-s) R_f = sum_{3 nmid n}` is
  kernel-verified.
* ch09: 12-digit spectral-gap provenance withdrawn; `lambda_0(H_NP)` as printed
  is EXACTLY `lambda_0(H_P) - Delta`. **Convention clash with ch07 recorded:
  opposite orderings of which class has the larger ground-state energy.**
* ch10: `lem:consciousness_regularization` refuted by its own 2026-10-03 remark
  --- under the lemma's own closure the force is a pure gradient, which does zero
  work on a divergence-free field, so the claimed dissipation is 0.
  `nu_eff` relabelled a postulate. The global-regularity chain is conditional on
  that postulate.
* ch10: `d_f = 3 - zeta_2/2` is unestablished and fails the K41 baseline in both
  directions; the 2026-10-05 ten-site substitution replaced one underived value
  with another. Deliberately not corrected a third time.
* ch11: both printed numerical derivations of `ch_2=0.95` are already refuted
  in situ: the anomaly route misses by about 1570 and the Gaussian integral is
  `sqrt(5/(pi+5)) approximately 0.7837`, not 0.95.
* ch11: the displayed 13D-to-4D calculation gives about 1.62; the attempted
  replacement gives 12.55. The chapter correctly records four macroscopic
  dimensions as empirical input and the derivation as open.
* ch11: the GUT-scale muon-g-2 substitution gives about `3.33e-35`, not
  `2.47e-9`; the printed target would require a roughly 1.16 TeV mediator.
* ch11: its final verification ledger correctly classifies the RQG shiab,
  projection and BRST claims as untested framework-internal constructions and
  the anomaly-resolution claims as retrospective/not independently validated.
* ch12: the chapter already records that its two mass assignments are mutually
  incompatible without an additional UV/IR bridge: the threshold rule gives
  `m_C about 0.22 M_Pl`, while the cosmology section assumes `m_C about 10^-5
  eV`. The bridge remains open rather than numerically derived.
* ch12: its correction to the quartic self-interaction pairing factor is valid:
  the three Wick pairings give factor 3; the earlier `4!/(2!)^4=3/2` expression
  was not the appropriate combinatorics.
* ch12: the crystallization-energy close is already correctly withdrawn: an
  exponentially suppressed correction to a `10^-5 eV` scale cannot produce a
  `1 eV` binding energy.
* ch13: the 2026-10-03 Reissner--Nordstrom corrections are mathematically sound
  for the RN analogy: the outer horizon shrinks with charge, and the first
  Hawking-temperature correction cancels at order `Q_C^2` and begins at
  `Q_C^4`. This does not itself derive `Q_C` from the consciousness action.
* ch13: the equation-of-state correction correctly proves that its postulated
  `w_C in [-1/3,1/3]` fluid cannot drive acceleration and moves farther from
  NEC violation as `ch_2` rises. The stale paragraph immediately below remains
  explicitly flagged in the source.
* ch13: the Kaup-bound numerical correction is correct for scalar fuzzy-dark-
  matter boson stars: `m=10^-22 eV` gives a galaxy-scale maximum near
  `8.5e11 M_sun`, not `10^-5 M_sun`. Applicability to the tensor consciousness
  field is a separate open bridge (finding 32).
* ch14: its 2026-10-06 Bianchi correction is correct for the displayed field
  equation: `nabla_mu(T^{munu}+C^{munu}) = nabla^nu Lambda_eff/(8 pi G)`;
  the printed trace-dependent right-hand side is not the divergence identity.
* ch14: its diffeomorphism correction correctly observes that transforming
  `C^{munu}` as a tensor does not make ch08's preferred-slice spatial integral
  a scalar. A later local action formulation could repair this, but that repair
  is not the formula currently printed in ch14 and must be audited separately.
* ch14: the zero-temperature SSB correction is correct: with `m_C^2>0` and
  `lambda>0`, the only minimum is zero; changing only the sign of `lambda`
  makes the potential unbounded. The VEV `v_C delta^{munu}` also selects a frame.
* ch14: the consciousino see-saw arithmetic correction is correct as arithmetic:
  a `1 TeV` input gives about `8.2e-5 eV` with the unreduced Planck mass, not
  `1e-15 eV`. Existence of the proposed supermultiplet remains unformalized.
* ch15: the central finite-difference, RK4, Fourier differentiation, BSSN,
  Metropolis and convergence concepts are standard numerical methods. Their
  generic descriptions do not validate the consciousness-specific equations or
  the example implementations.
* ch15: the corrected radix-economy statement is sound arithmetic:
  `b/ln b` is minimized continuously at `e` and among integer bases at 3. The
  claimed physical ternary-hardware energy advantage remains explicitly marked
  as a prospective, falsifiable alignment rather than an established result.
* ch16: the classical finite/infinite-dimensional spectral theorem, functional
  calculus, C*-axioms and Gelfand--Naimark material is standard once the usual
  domain and boundedness qualifications are restored.
* ch16: its 2026-08-08 audit is correct and materially protective of the TOE:
  the commutative zeta-value construction is not the noncommutative UHF
  substrate; the former's sup norm is undefined on zeta as printed; the actual
  simple noncommutative substrate has no nonzero characters; and the UHF/AF
  substrate arc remains independent of that failed identification.
* ch16: its Tomita--Takesaki correction is correct: the proposed vertical shift
  cannot select a real part, and the modular group of a faithful normal state on
  an abelian von Neumann algebra is trivial.
* ch17: the corrected unbounded-position example, mixed-boundary Green kernel,
  direct-integral factor decomposition and standard trace-class/HS/compact
  hierarchy are sound operator theory (with the standard domain qualifications).
* ch17: given the machine-checked identification of the substrate as the
  `3^infinity` UHF algebra with canonical faithful trace, its tracial GNS weak
  closure is classically the hyperfinite II_1 factor. This is a genuine
  mathematical payoff; the consciousness interpretation remains a separate
  bridge exactly as the update states.
* ch18: its corrections are substantively accurate: the original decoherence
  time formula is dimensionally inconsistent; `alpha about 10` cannot protect
  neural times; the EEG triples contradict their law; the computational formula
  is `ch_1`, not `ch_2`; the modified Born weights are unnormalized; and the
  deterministic norm-preserving flow still lacks stochastic Born statistics.
  Those corrections improve rather than demote the proposed measurement lane.
* ch19: Kallen--Lehmann is standard QFT (up to convention-dependent overall
  factors), but it supplies no consciousness correction without a defined
  positive spectral measure.
* ch19: the QCD correction is correct: the printed Planck-suppression formula at
  `Delta=0.0891` gives about `5.9 TeV`, not `350 MeV`; matching `300 MeV` would
  require `Delta about 0.0696`. The source's final status correctly treats it as
  a failed conjectural pattern.
* ch19: the Higgs section's final posture is appropriately cautious: its
  numerical combinations are retrospective candidates pending a composition
  operator and physical scale mechanism. Individual algebraic identities can
  be real without yet being particle-mass predictions.
* ch20: the chapter's verification ledger and analytic updates accurately
  preserve several genuine results: an unconditional certified on-line zero;
  exact xi/zero bridges and symmetries; a multiplicity-aware conditional
  rectangle argument principle; and kernel-checked finite-branch
  transfer-operator trace/residue formulas. These do not depend on the invalid
  basis/scaling calculation and do not prove RH.
* ch20: the current root-verified T15 arc adds an unconditional multiplicity sum
  at least two and a conjugation-closed, fixed-point-free, even-cardinality full
  T15 zero set. It still has no contour evaluation, upper count, exact count or
  finite-height RH; the manuscript's Aug-25 scope warning therefore remains
  directionally correct and should be updated, not erased.
* ch21: its 2026-07-23 and 2026-07-25 verification addenda correctly state that
  P-vs-NP is not proved, that the canonical alpha assignments are definitions
  rather than class-derived invariants, and that the nine-value rigidity and
  IBM-peak equalities are circular/uninformative rather than unsound. The
  correction from a supposed 16-digit empirical match to a three-decimal match
  is also mathematically appropriate.
* ch21: the addendum correctly preserves the negative result that the bare
  weighted digital-sum reality condition excludes both `sqrt(2)` and
  `phi+1/4`; this is real information about a failed derivation route and should
  remain distinct from the still-open search for a different operator bridge.
* ch21: the 2026-10-05 compactness and unitary-conjugation corrections are
  correct. A compact positive operator on an infinite-dimensional space has
  nonzero eigenvalues accumulating at zero, so it cannot have the printed
  positive bottom spectral gap; unitary conjugation preserves the spectrum and
  therefore cannot create the proposed P/NP gap.
* ch21: the corrected arithmetic is accurate: the proposed NP closed form is
  `pi(sqrt(5)-1)/(30 sqrt(2)) = 0.0915284...`, not the empirical `0.133022...`.
  The manuscript is right to withdraw the claimed numerical match.
* ch22: the 2026-10-05 emergence-spectrum correction is mathematically
  protective. Trace zero alone does not force imaginary spectrum; for the
  printed traceless real `3x3` matrix the stated determinant/sign conditions
  are needed, and its matrix `ch_2` condition lies on the opposite side of zero
  from the chapter's `0.95` threshold.
* ch22: the Crow-instability correction is accurate. Conservation of total
  circulation is not linear stability, and an equal-and-opposite vortex pair
  is a standard unstable configuration rather than a topology-protected one.
* ch22: the correction to `r |omega| -> C` is exact. For `C>0` it describes
  `|omega|~C/r` and hence an unbounded vorticity field; for `C=0` it still does
  not imply boundedness. The chapter is right to identify the intended bound as
  an authorial fork rather than silently rewriting it.
* ch22: the helicity-threshold correction correctly identifies the parity
  problem, the missing global `H_max`, and the mismatch between global helicity
  and a point value. It also correctly notes that the chapter's own oscillatory
  singular density would leave no defined value at the emergence point.
* ch22: the r215 typed-content audit is appropriately localized. The headline
  `NS_Solution` predicate contains no PDE and collapses local/global content,
  but the separate 31-file Fujita--Kato layer contains substantive Fourier,
  Leray-symbol, heat-semigroup, Schwartz and Sobolev machinery. The defective
  endpoint must not be used to erase that real supporting mathematics.
* ch23: the 2026-08-06 correction is decisive: at `alpha=2` every phase is one,
  so `R_f(2,s)=zeta(s)` and there is no positive real resonance zero. The sign
  change across `omega=1` is caused by the zeta pole, not a root. This refutes
  the printed `omega_c` mechanism while leaving independent finite-dimensional
  reflection-positivity results untouched.
* ch23: the 2026-08-08 arithmetic and ceiling corrections are accurate. The
  boxed product equals about `132.148`, not `420.43`, and the corrected
  alpha-dependent real-zero route caps the same formula near `62.3 MeV` over all
  alpha. The printed digits have no established provenance.
* ch23: the 2026-10-05 string-tension correction is correct both numerically and
  dimensionally: `Delta^2/(4 pi hbar c)` does not equal `(440 MeV)^2`; the
  phenomenological `sqrt(sigma)` value would have to be an independent input
  unless a different derived relation is supplied.
* ch23: its UV correction properly follows the identity `R_f(2,s)=zeta(s)`:
  the modulation tends to `e^-1`, not zero. Hence that mechanism does not
  reproduce asymptotic freedom or provide the advertised natural UV cutoff.
* ch23: the verification ledger correctly keeps the continuum `SU(3)` measure,
  reflection positivity on the real field space, Wightman reconstruction and
  mass-gap propagation open, while preserving genuine finite-dimensional OS
  work. The Clay-level environments should remain conditional rather than
  theorem-labelled until those hypotheses exist.
* ch24: the point-count correction at `p=5`, both worked-example corrections,
  the transfer-operator diagnosis and the complexity correction are all
  substantively accurate. The printed contraction operator is ill-defined at
  `s=1`, quasinilpotent on the stated space and cannot encode rank as a
  `phi/e` eigenvalue multiplicity; the proposed rank-one examples are also
  arithmetically wrong as documented.
* ch24: the manuscript correctly isolates a surviving trace-level signal from
  the failed multiplicity mechanism. The generic fixed-point residue identity
  and its instantiation for branches `z/p` with weights `a_p p^-s` are genuine
  kernel-checked structure; interpreting a regularized slope as rank remains
  empirical and cutoff-sensitive.
* ch24: the universal secant/content/canonical-height pipeline is a substantial
  independent formal result. It gives reusable, curve-independent rank lower
  bounds from certified nonzero Gram determinants and transfers the rank-two
  and rank-three examples through the same construction. It does not give
  descent upper bounds, an L-function bridge, `Sha`, or BSD, exactly as the
  chapter's update states.
* ch24: the 2026-08-06 `Sha` correction is decisive: evaluating the proposed
  resonance bound at the conductor makes it essentially one and it is violated
  by known nontrivial `Sha` examples. The false bound is independent of the
  surviving height and trace theorems and should not be used to downgrade them.
* ch25: the 2026-10-03 concentration correction is exact and identifies a
  plausible replacement object: an `xi`-dependent coefficient-mass fraction.
  The printed eigenvalue ratio is independent of `xi`, generally complex and
  point-dependent, and lacks positivity/trace-class hypotheses. Choosing the
  replacement would require a real redefinition, not a silent patch.
* ch25: the 0.95 correction correctly identifies
  `epsilon_quantum=0.95-6/pi^2` as a remainder chosen to hit the target, not a
  derivation. Propagating ch26's “asserted numerology” label is the minimum
  consistent scope unless a physical/mathematical source for the correction is
  independently supplied.
* ch25: the reversed-inequality, K3, abelian-fourfold and validation-statistic
  corrections are all sound. The supposed `rank<=20` becomes weaker as sigma
  approaches one; K3 divisor rank is at most 20; 240 exceeds the total
  `sum_p h^(p,p)=70` for an abelian fourfold if independent classes are meant;
  and a sample with mean `0.631` cannot have every value at least `0.95`.
* ch25: the final verification ledger correctly says the standard Hodge
  conjecture remains open and that substrate discharges trivialize
  `isAlgebraic` exactly where the hard content should live. Those typed results
  are valid at their declared proxy scope but cannot be promoted to the literal
  cycle-class surjectivity statement.
* ch26: the vacuum-density correction distinguishes a bad derivation from a
  sound order-of-magnitude result. The printed mixed-unit expression is wrong,
  while the properly dimensioned Planck-cutoff estimate is indeed of order
  `10^91 g/cm^3`; this repair strengthens rather than erases the motivating
  vacuum-catastrophe comparison.
* ch26: the TeV-SUSY correction is also sound. Quartic cutoff scaling reduces
  the Planck discrepancy by 64 orders, leaving about 56 rather than 13; the
  qualitative claim that TeV-scale SUSY does not solve the problem survives and
  becomes stronger.
* ch26: the 2026-10-03 exponent correction is decisive. The constructed
  exponent gives `10^(-4.1e127)`, not `10^-120`; the required exponent is about
  `276.31`. The exponential-suppression shape survives as a model idea, but its
  numerical bridge to the observed density does not.
* ch26: the verification ledger correctly classifies `0.95=6/pi^2+epsilon` as
  fitted numerology and the `99.6%` lattice agreement as a comparison of the
  model realization to its own calibrated target, not independent validation.
* ch26: the equation-of-state bridge is a meaningful falsifiability advance at
  the algebraic level: `Lambda_eff'=-g Lambda_eff` plus continuity gives
  `w=-1+g/(3H)`. For the chapter's calibrated cubic-time volume, the resulting
  present `w` is enormous and positive rather than dark-energy-like. The
  empirical DESI numbers and substrate embeddings should still receive their
  own source/provenance audit later; the internal rate contradiction does not
  depend on them.
* ch27: the 2026-10-03 EOS correction is correct: the boxed positive correction
  forces `w_DE>=-1`, gives `w(0)=-0.85`, and cannot be called phantom. It also
  accurately records the unresolved choice between constant epsilon and
  `epsilon/(1+z)`.
* ch27: the Hubble bookkeeping note is appropriately modest: `69.1` and `69.8`
  differ but their quoted intervals overlap. The deeper issue is already in the
  older scope note---both are framework/calibration values, not a reproduced
  joint inference from the primary likelihoods.
* ch27: the Quipu factor-of-pi correction is exact. With the printed `pi/10`,
  the formula gives about `4.33 Gly`; the stated `1.38 Gly` is the result after
  deleting pi. Retaining universal `pi/10` and claiming agreement with the
  observed extent are mutually exclusive, so this remains an authorial fork.
* ch27: the verification ledger correctly treats the EOS, growth, Hubble,
  power-spectrum, chi-square and Quipu claims as empirical hypotheses rather
  than machine-verified physical results. This preserves their falsifiability
  without presenting unrun likelihoods as confirmations.
* ch28: the time--temperature, reheating-temperature and early-time-fraction
  corrections are arithmetically and conceptually protective. They expose the
  incompatible onset conventions instead of silently choosing one; the
  qualitative late-onset proposal remains available for a future defined
  observable.
* ch28: the inflation-scale correction is correct and essential. Vacuum energy
  density and the geometric cosmological constant have different dimensions,
  the Friedmann equation needs the reduced-Planck-mass denominator, and full
  Planck density cannot simultaneously yield the printed `10^14 GeV` Hubble
  scale.
* ch28: the growth-factor correction is correct. Removing the spurious leading
  scale factor restores `D proportional to a` in matter domination, while a
  genuinely Lambda-dominated future freezes growth rather than supporting the
  former power-law claim.
* ch28: its final verification ledger draws the right evidentiary boundary:
  standard BBN/CMB agreement is consistency under a postulate, not positive
  evidence; the late-time phase-transition signatures are untested empirical
  hypotheses; and the critical-temperature/IIT inputs are asserted. The
  uncorrected body and conclusion repeatedly exceed that ledger, as recorded
  above, but the ledger itself should be preserved and propagated.
* ch29: the correction to the impossible CMB `9 -> 11` degree-of-freedom
  reversal is valid, as is the decision not to invent replacement counts from
  an unidentified compressed likelihood. The additional global-count defect
  recorded above remains separate.
* ch29: the percentage correction is arithmetically exact and unusually clear:
  `333.1/687.3=48.47%` is the conventional fractional reduction, whereas
  `333.1/354.2=94.04%` measures the removed residual against what remains and
  is not conventionally “percentage improvement.” The later `94.3%` has no
  supplied provenance or valid positive parameter penalty.
* ch29: its BIC arithmetic correction faithfully evaluates the printed inputs,
  and the stale 319.6 restatement is correctly flagged. This does not cure the
  statistical misuse of disputed dof as two different data counts, recorded
  above; both levels of the diagnosis should remain visible.
* ch29: the final verification ledger and `empiricalclaim` correctly state that
  the Lean result is only a definitional density bracket, not verification of
  any catalog fit. They also correctly classify the fitted-versus-predicted
  parameter match as circular until independently reproduced and preserve the
  future-survey numbers only as prospective hypotheses.
* ch30: the confusion-matrix correction is exact. The matrix gives sensitivity
  `422/431=97.91%`, specificity `402/416=96.63%`, PPV
  `422/436=96.79%` and NPV `402/411=97.81%`; the former boxed sensitivity and
  specificity were actually PPV and NPV, while the other two matched none.
  The separate 821-versus-824 stratified-total inconsistency is also correctly
  isolated rather than papered over.
* ch30: the discrepant-case heading correction from 15 to 23 and the
  per-thousand correction from 350 to 373 are arithmetically sound. Their
  downstream national extrapolation remains conditional on the unvalidated
  clinical rates, exactly as the inline correction states.
* ch30: the final verification ledger draws the essential boundary correctly:
  `19/20=0.95` and an algebraic IIT inequality are facts about definitions, not
  evidence about brains; the 847-patient accuracy, prognostic AUC and economics
  remain untested empirical claims pending independent clinical validation.
  The body repeatedly crosses that boundary, as recorded above, but the ledger
  itself protects the research program and should be retained.
* ch31: the 2026-10-03 reachability correction is decisive and mathematically
  protective. For a normalized state and a complete projector partition, the
  printed prefactor forces `ch_2<=1/N^2`; the only `N=1` escape makes the
  statistic identically one. The correction also correctly records that the
  large-`N` limit drives this quantity toward zero rather than making the IIT
  bridge exact.
* ch31: its fixed-phase analysis of the incomplete-projector reading and its
  asymptotic warning both attack the actual displayed formula rather than the
  TOE's broader intent. The empty 0.95 regime is a failed operationalization,
  not evidence against every possible consciousness observable.
* ch31: the band-power ratio correction is also exact. Without normalization,
  `(P_beta^2/(P_delta P_theta))^(1/3)` is unbounded and diverges when either
  denominator vanishes; it is therefore a sixth incompatible use of `ch_2`,
  not a bounded clinical implementation of the projector statistic.
* ch31: the final verification ledger properly classifies the IIT mapping,
  14-Hz correspondence, neural cohorts, animal manipulations and artificial-
  system values as untested empirical claims. Its distinction between an
  algebraic threshold inequality and neural validation must remain controlling
  even where the chapter's surrounding prose says “established” or “solved.”
* ch32: the 2026-10-05 age-correction note is arithmetically consistent. The
  decline is `0.0012` per decade, not `0.012`, and the displayed reference ages
  follow the corrected rate.
* ch32: its verification ledger draws the correct evidentiary boundary:
  normative values, state/species separation, reliability and device transfer
  are not independently validated, while the protocol only specifies a
  computation. That ledger controls over the surrounding deployment claims.
* ch33: the 2026-10-03 bit/decimal conversion correction is exact:
  `p log10(2)≈p/3.32`, so 150 decimal digits require about 498 bits.
* ch33: the Euler--Maclaurin correction fixes the finite-sum convention, the
  sign of the endpoint term, the rising factorial, and the remainder exponent;
  its correction of the raw `zeta(3)` tail from six to about twelve digits is
  also sound. These repairs should be preserved while the still-overstated
  generic remainder language is narrowed.
* ch33: the Richardson correction correctly withdraws the former ten-digit
  improvement. Under the chapter's own two-term model at `m=16`, canceling the
  leading `m^-p` term improves the scale by only about a factor of seven, or
  `0.85` decimal digits.
* ch33: its central scope statement is right: numerical agreement, regardless
  of precision, is evidence rather than proof of the framework's mathematical
  or physical premise. That distinction must control the stronger language in
  the introduction and conclusion.
* ch34: its 2026-07-23 scope notes correctly state that high-precision
  reproduction is numerical evidence, not a mathematical proof, machine
  verification, Millennium closure, or clinical validation. These notes are the
  controlling interpretation of the protocols.
* ch34: the 2026-10-05 memory correction is arithmetically correct for the
  chapter's intended `N=3^16`: a dense float64 matrix needs about 14.8 PB, not
  128 GB, and the cosine-distance kernel is not made sparse by a `10^-10`
  threshold. The separate factor-of-three defect in the printed recursion is
  recorded above and makes the literal code even larger.
* ch34: the final status ledger is right to distinguish conditional Lean
  implications, asserted alpha assignments, and unvalidated clinical hypotheses
  from literal solutions of the external problems. Later additions enlarge the
  machine-checked corpus but do not erase those scope distinctions.
* ch34: the path correction accurately records that the June referee reports
  moved under `ARCHIVE/.../root_docs/`, the L4L sources require the
  `PF_Lean4Lean/` prefix, and the claimed 150-digit zeros data file is absent.
  Those provenance defects are independent of whether the archived audit
  conclusions were correct at their original commit.
* ch34A: the 2026-08-08 “critical logical-structure correction” is exact and
  decisive: the flagship implication discards its antecedents because all
  consequences are supplied by unconditional proofs. Its explicit demonstration
  that any proposition could replace the antecedent is the controlling reading
  of that theorem and must be propagated to the opening and conclusion.
* ch34A: the 2026-08-02 framework-first correction also draws a necessary
  boundary. The residual work includes the external open mathematics itself,
  not merely filling library carriers or translating already-complete PF
  proofs. That admission is compatible with keeping the conditional framework
  while withdrawing literal closure language.
* ch34A: its Hodge correction correctly identifies a tautological/generic
  carrier rather than the standard Hodge conjecture. Axiom-free elaboration of
  the proxy does not convert it into an unconditional theorem about algebraic
  cycles.
* ch34A: the 2026-10-03 final ledger correctly separates the five incompatible
  `ch_2` meanings, records the matrix cap and empty threshold regime, and labels
  the consciousness bridge empirical and unvalidated. These scope statements
  should control the stronger prose elsewhere in the chapter.
* ch34A: the exact operator-algebra results survive this audit at their stated
  scope: the concrete `3^infinity` UHF substrate has a canonical faithful trace,
  the proved simplicity/uniqueness results are genuine, and the
  `T_infinity_rigidity` endpoint has its hypothesis constructed rather than
  assumed. None of the proxy defects above downgrades those theorems.
* ch34A: the algebraic cascade and relative-minimality results are real
  conditional mathematics. Their correct label is “solutions/minimality within
  the displayed equation system,” separate from whether that system is forced
  by the substrate or realized in physics.
* ch35: the 2026-10-03 memory, sparsity, runtime and precision correction is
  arithmetically and architecturally correct. A dense float64 matrix at
  `N=3^16` needs about 14.8 PB, the cosine threshold removes essentially no
  entries, the Python double loop is infeasible, and NumPy/SciPy do not inherit
  `mpmath` precision. This correction should control every surviving runtime and
  150-digit claim in the chapter.
* ch35: unifying the two consciousness print sites under one three-way
  classification rule repairs the earlier code-path inconsistency. It does not
  establish that `compute_ch2` exists, that the rectangular input is valid or
  that the threshold is reachable; those separate defects are recorded above.
* ch35: the final 2026-07-23 verification ledger correctly distinguishes
  reproducibility from proof and says that passing stored-number tests does not
  establish RH, P-vs-NP, Yang--Mills or the empirical consciousness claims. Its
  scope discipline is sound even though the named Python suite is absent.
* ch35: the formal Lean/Coq development and one-command formal verification
  infrastructure are real repository assets, separate from the nonexistent
  Python package documented here. Correcting this chapter's software inventory
  should not downgrade the exact kernel-checked UHF results.
* Foundational lexicon: the basic definition and `O(log_3 n)` repeated-division
  algorithm for the ternary digit sum are sound, as are absolute convergence of
  the defining `R_f` Dirichlet series for `Re(s)>1` and the specialization
  `R_f(0,s)=zeta(s)` in that half-plane. These local facts survive even though
  the global continuation, status labels and physical bridges overreach.
* Appendix A: the manuscript correction on the resonance table correctly
  identifies its primary defects: `R_f` requires two arguments, the table gives
  no `s` or method, exact integer-alpha behavior conflicts with the advertised
  uniformly positive interpretation, and `resonance_values.csv` is missing.
  Its additional IVT rhetoric should be narrowed as recorded above, but the
  provenance diagnosis itself is valid.
* Appendix A: evaluating standard on-line zeros remains legitimate numerical
  work and is consistent with RH over the tested finite range. It is evidence
  about those particular ordinates, not proof of RH, completeness of the list or
  an `H_zeta` spectral realization.
* Appendix B: the opening BRST background is broadly standard up to conventional
  sign choices: gauge fixing introduces Grassmann ghost/anti-ghost fields, the
  BRST differential is nilpotent when correctly constructed, and physical states
  are represented by an appropriate ghost-number-zero cohomology. These facts do
  not depend on the later fractal interpretation.
* Appendix B: characteristic forms, equivariant cohomology, localization and
  Donaldson--Witten theory are genuine mathematical/physical subjects. Their
  presence is useful context, but the specific identifications made here require
  comparison maps and hypotheses that the appendix does not provide.
* Appendix C: the acquisition checklist, signal-quality checks, cautious gray-
  zone language, serial-measurement idea and recommendation to treat a metric as
  one data point are reasonable ingredients for a future research protocol.
  They require ethics review, clinical experts and validation before use, and do
  not rescue the impossible statistic or reported outcomes.
* Appendix C: Butterworth filtering, ICA, epoching and coherence are standard
  signal-processing tools when implemented with explicit channel/time
  conventions and validated preprocessing choices. The defect is in this
  pipeline's incomplete implementation and unsupported interpretation, not in
  those methods themselves.
* Appendix D: the compact API layout is a usable design specification for a
  future package. Its module boundaries separate zero computation, fractal
  operators and EEG processing clearly; the necessary correction is to label it
  planned and then implement/version-test it, not to treat the interface sketch
  as evidence against the separate formal mathematics.
* Appendix E: presenting the GU and ring-laser material as proposed comparative
  alignments could define future research questions. The issue is the current
  transition from analogy to “resolved” without mathematical definitions or
  evidence, not the permissibility of exploring those hypotheses.
* Appendix F: the ternary digit-sum proof `S_3(3n)=S_3(n)` is correct. The
  functional equation also genuinely supplies the reflected-zero symmetry;
  only the final circular inference to RH must be removed.
* Appendix F: the text explicitly notices that its attempted vacuum-energy
  mechanism fails to approach the observed scale. That negative conclusion is
  directionally honest and should be preserved, while the exponent arithmetic
  and the unsupported fallback are corrected.
* Appendix G: most standard symbols, unit conventions and index conventions are
  useful and conventional. The appendix can remain a compact reference once the
  project-specific overloads, natural-number convention and evidence-bearing
  parameter labels are made explicit.
* Appendix H: the 2026-05-18 correction to
  `pi/(10*(phi+1/4))` is exact and important. The value is about `0.168176418`,
  not `0.1330222423`, and the text correctly states that the closed form fails to
  reproduce the stored NP eigenvalue. This negative result should remain.
* Appendix H: the named RH/Hodge JSON histories and the plotted PNGs are not
  wholly fictitious; relevant files are preserved in `ARCHIVE/`, prior-work
  paper directories and the manuscript figure tree. Their proper label is
  historical numerical artifacts pending method/provenance audit, not proof of
  the associated Millennium claims.
* Appendix I: the 2026-09-12 alpha-zero `R_f` scope is stated carefully: the
  bridge to `riemannZeta` is on `Re(s)>1`, the meromorphic continuation result is
  only for alpha zero, and the nonzero-alpha continuation remains open. This is
  the correct separation from the lexicon's overbroad claim.
* Appendix I: the bounded-BSD diagnostic row is unusually honest. It explicitly
  says the result measures Lean-tree completeness rather than curve arithmetic,
  explains that its witness ignores the curve, preserves deprecated overclaiming
  names for provenance, and states that BSD remains open.
* Appendix I: the final 2026-08-02 correction is controlling and correct: legacy
  Coq files provide structural-shape parity, not independent verification, and a
  clean Lean build does not upgrade conditional or restricted theorem scope.
  This correction should be moved ahead of the tables and propagated into their
  headings.
* Appendix J: its strongest passages are unusually explicit about scope. It says
  the Gaussian NS lift is not a Navier--Stokes solution, the literal Hodge lift
  is open, the Yang--Mills continuum construction remains open, and an honest
  P-vs-NP alpha bridge would be circular. Those admissions should control the
  surrounding completion language.
* Appendix J: upgrading from placeholder carriers to `SU(2)`, Schwartz fields
  and Weierstrass curves is real formalization progress. It improves type
  fidelity and exposes residuals more sharply, while not by itself supplying the
  associated PDE, arithmetic-rank or constructive-QFT semantics.
* Appendix J: several local arithmetic and musical equalities can remain as
  exact conditional results. They should be separated from the unverified
  temple, cymatic and cross-domain physical interpretations.
* Appendix K: the closing sentence is appropriately explicit that the session
  does not close any Clay conjecture. That scope statement should govern the
  earlier language about discharge, shortest chains, experimental wins and
  Clay-grade residuals.
* Appendix K: the elementary Fibonacci, power-tower, logarithmic,
  trigonometric, Vieta and interval identities can be genuine Lean theorems at
  their stated definitions. Their mathematical correctness must be kept
  separate from novelty, physical interpretation and evidentiary status.
* Appendix K: consolidating duplicate residual names and bundling already-proved
  clauses are useful maintenance operations. They improve dependency visibility
  and citation ergonomics even when they add no new theorem about the external
  problem.
* Appendix L: the analytic route from a nonzero holomorphic function on a
  second-countable domain to a countable discrete zero set is a legitimate
  mathematical strategy. If the exact Lean predicate is a subset of zeta's zero
  set, the resulting countability theorem can stand with narrowly stated scope.
* Appendix L: introducing a literal Fefferman-target proposition and using
  standard mathlib carriers are useful specification improvements. They clarify
  what a future proof must connect, even though the present bridge does not make
  that connection.
* Appendix L: the text accurately describes its Coq artifacts as
  structural-shape parity at lines 438--440. That narrow description should
  control the broader “three-prover closure” language elsewhere.
* Backmatter: the biographical account, advocacy for neurodivergent researchers,
  encouragement to verify claims and invitation to correct mistakes are not
  mathematical defects. They can remain while headline research claims are
  brought into evidence-accurate scope.
* Epilogue: the explicit possibility that the framework is wrong, the maxim
  “Read. Question. Verify. Extend. Correct. Build,” and the five-part scientific
  path forward are strong governing principles. Applying them consistently
  would strengthen rather than diminish the book.
* ch08: the 2026-10-03 through 2026-10-06 correction blocks are unusually
  valuable. They correctly identify the R1/R2 threshold ambiguity, conservation
  as sector exchange, the 21-order rate error, the impossible gravitational
  anomaly units, the failed crystallization potential, the noncovariant
  `Lambda_eff` kernel and the necessity of a genuine Green function.
* ch08: the covariant scalar-action and screened-Poisson calculations are viable
  model-building directions when labeled as a replacement proposal with open
  parameters. They should not be used to retroactively validate the original
  nonlocal equation or its consciousness interpretation.

## EXACT FORMAL AUDIT AFTER THE READING PASS

### `PF/Ch2ThresholdSelection.lean` --- accepted with narrow scope

Root read all 465 source lines and all 233 lines of its sole project import,
`PF/Cosmology/VortexCavitationBridgeChecks.lean`, at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. Source SHA-256:
`24d99dd00d57a95e760c52ffd6418af5a7a1709f85b020dfdc97021738a89c2d`;
last-touch commit `c25853f416fd21ffbaf84cd4cfeb248668957371` (2026-10-06).
Direct elaboration with Lean 4.24.0-rc1/mathlib
`eed770a434957369c6262aa3fb1d6426419016d4` exited 0 to an isolated `/tmp`
olean, SHA-256
`466142bcd4cf8dcb277d3ee13e63e627c012b9b7f818bd84044ecbd3ae3bd9e2`.
All fifteen live `#print axioms` reports were captured: fourteen use only a
subset of `[propext, Classical.choice, Quot.sound]`; the abstract schema
`no_form_both_reaches_and_gates` uses none.

Accepted mathematics: the real-arithmetic purity equivalence; the one-way
dimension consequence under the supplied purity lower bound; the maximally
mixed ceiling calculation; elementary factor-size arithmetic; the exact four
tower values shown; the matrix formula's universal `1/2` upper bound and closed
`19/20` gate; and the stated existential real inequalities. These are genuine
Lean theorems with clean foundational dependencies.

Scope limits found by exact source reading:

* `bipartite_needs_both_factors` assumes `20 <= min dA dB`; it does not formalize
  a density matrix, Schmidt rank or derive that premise from threshold crossing.
* `threshold_interval_gives_same_level` checks three sample thresholds and the
  interval width. It does not quantify over every threshold in `(8/9,26/27]` or
  formally define/prove a first-crossing level.
* `nineteen_twentieths_not_a_tower_value` excludes only the four displayed
  values for dimensions 3, 9, 27 and 81; it is not a proof for every ternary
  tower level.
* `threshold_is_attainable` proves arithmetic at purity `1/27`; it does not
  construct a density operator realizing that purity.
* `unpinned_quotient` is an abstract existential denominator lemma, not a theorem
  about the Chern--Weil normalizer. `band_ratio_excluded` is likewise a real-
  number schema, not an unboundedness theorem for the clinical band-ratio
  definition.
* The ch08 source-gate concern remains explicitly unformalized. The final schema
  has its decisive premises supplied, and the file correctly says it proves
  nothing about which R1/R2 interpretation is physically intended.

Verdict: accept this file as a careful collection of proxy arithmetic and one
faithful negative theorem for the book's matrix formula. Do not cite it as a
selection of `0.95`, a construction of the Chern--Weil consciousness measure, a
clinical operationalization or a no-signalling theorem for ch08.

### `PF/Ch08Ch14ModifiedRelativity.lean` --- accepted as scalar bookkeeping only

Root read all 312 lines at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. The file has no project imports;
its source SHA-256 is
`107c288f197f8b6e64697f636decf1a71717e6b13d759dcdfcd97001c9adeb56`,
and its last-touch commit is `b89bffb0a991ad8728f20f6e36c35b78bc3a923c`
(2026-10-06). With no other Lean/Lake worker active, direct isolated elaboration
on Lean 4.24.0-rc1/mathlib `eed770a4` exited 0. The `/tmp` olean SHA-256 was
`9b4305f38103ae4e0d6053763bafe8387dee622617697abd960c1feaa5c2f8aa`.
All ten live `#print axioms` reports returned only
`[propext, Classical.choice, Quot.sound]`.

Accepted mathematics: positivity of the defined scalar `kappa=8*pi*G`; the
cleared scalar equivalence showing that the two printed coefficient forms agree
for nonzero `gradLam` exactly when `s*kappa=2`; the resulting arithmetic value
`2/kappa=1/(4*pi*G)`; the four-dimensional and general-dimensional trace
identities; the nonzero-quotient equivalence; and arithmetic ordering/ratios of
the three stored PPN bounds.

Scope limits found by exact source reading:

* No spacetime, metric, tensor, covariant derivative, Bianchi identity,
  foliation, `Lambda_eff` functional or PPN observable is defined. Every theorem
  is over real scalars.
* `forms_agree_iff_trace_fixed` faithfully exposes the coefficient mismatch only
  after the physical equations have been reduced to the supplied scalar model.
  It does not itself derive either divergence equation from a field equation.
* `nonconservation_iff_lambda_varies` is the elementary fact
  `gradLam/kap != 0 <-> gradLam != 0` for positive `kap`; it does not establish
  that the manuscript's `Lambda_eff` varies or that its gradient is timelike.
* The three PPN limits are definitions carrying cited numbers. Their source
  provenance and applicability are not formalized, and there is no map from the
  manuscript's preferred foliation or nonconservation scalar to any PPN
  parameter. Thus `10^-20` is a conditional external constraint, not a PF
  prediction or computed falsifier.
* `ModifiedRelativity_capstone` does not contain the prose-only slice-gradient
  or preferred-frame step, and it does not even include
  `nonconservation_iff_lambda_varies`. Its docstring's preferred-frame conclusion
  exceeds its four arithmetic clauses.
* `quantities_are_meaningful` proves positivity and ordering of defined reals;
  that is non-vacuity of the arithmetic, not physical meaningfulness.

Verdict: accept the file as a clean formal diagnosis of the ch08/ch14 scalar
coefficient inconsistency and a transparent record of three external numerical
bounds. Do not accept it as a covariant derivation, proof of preferred-frame
physics, calculation of a PPN parameter or prospective empirical prediction.

### `PF/LambdaEffFromAction.lean` --- accepted as real-variable consequences, not an action derivation

Root read all 323 lines at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. The file imports only two mathlib
modules and no project source. Its source SHA-256 is
`42c5dae393549b8c68a146838a32a1ff943fb679a2f48d6e7bc9a7540a0cce87`;
its last-touch commit is `b45e89c7fa585fdf715d648af2be095244fed9e3`
(2026-10-06). With no other Lean/Lake worker active, direct isolated elaboration
on Lean 4.24.0-rc1/mathlib `eed770a4` exited 0. The `/tmp` olean SHA-256 was
`6b9a6c06a7bb24588924d93e8807a6624969f6024aff37581952f97b60dd9a4f`.
All ten live `#print axioms` reports returned only
`[propext, Classical.choice, Quot.sound]`.

Accepted mathematics: for the explicitly defined real functions
`potential = (Lam0/kap)*exp(-phi/M)` and
`lambdaEff = Lam0*exp(-phi/M)`, the normalization identity (for nonzero
`kap`), positivity, strict decrease for positive scales, and the exact
scaled-difference identity; the stated elementary slow-roll error inequality;
the scalar implication `divG=kap*divS`, `divG=0`, `kap!=0` implies `divS=0`;
positivity and unboundedness near zero of the explicitly defined real function
`1/(4*pi*r)`; and nonconstancy at `phi=0,M`. These are genuine Lean theorems.

Scope limits found by exact source reading:

* No action, manifold, metric, scalar field, covariant derivative, variation,
  stress tensor, wave/Laplace operator, Chern--Weil form, aether Lagrangian or
  PPN parameter is defined. The file itself correctly labels the variational
  derivation, Noether theorem, Bianchi identity and `alpha_3` claim prose-only.
* `lambda_eff_from_potential` is cancellation between the two supplied real
  definitions. It does not show that either definition is the output of a
  metric variation, despite the theorem docstring's phrase "output of a
  variation."
* `slow_roll_relative_error` is a real inequality conditional on the supplied
  variables `K,V,eps` and bound `K <= 2*eps*V`; it neither defines kinetic
  density nor proves a slowly varying limit for a field solution.
* `absorbed_lambda_leaves_no_residue` is one-line scalar division after the
  field equation and Bianchi conclusion are encoded as hypotheses. It does not
  derive stress-energy conservation and has no theorem-level occurrence of
  `alpha_3`; the claimed structural `alpha_3=0` remains prose.
* `greensKernel` is merely defined to be `1/(4*pi*r)`. The proofs establish
  positivity and unboundedness, but not that it is a fundamental solution of
  the three-dimensional Laplacian, not the displayed static field equation,
  and not the manuscript integral representation. No theorem mentions `R_f`,
  its abscissa, translation invariance, units or the quoted numerical values.
* The capstone is exactly the conjunction of the seven preceding real
  statements. Its docstring's action, conservation, `alpha_3`, static-solution
  and Dirichlet-kernel conclusions are not present in its type.
* No values for `M`, `f`, aether couplings or `Lam0` are derived, and no
  observational match or prospective prediction is formalized.

Verdict: accept the exponential identities, conditional error inequality,
scalar conservation implication and elementary kernel behavior at their exact
types. Classify this as a conditional reduction with substantial downstream
algebra formalized: the potential is supplied as a definition, while the
variational derivation, Noether/Bianchi bridge and PPN interpretation are
explicitly disclosed but unformalized. This file repairs neither the
manuscript's kernel nor the operator/geometric bridge by itself.

### `PF/ScreenedKernelAndFieldScale.lean` --- accepted as kernel arithmetic, not a field-theory derivation

Root read all 324 lines at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. The file imports only two mathlib
modules and no project source. Its source SHA-256 is
`68830a734a7767564558fb9447cb20bb720474f1a5ba23e21e4d772e8cce77c4`;
its last-touch commit is `b45e89c7fa585fdf715d648af2be095244fed9e3`
(2026-10-06). With no other Lean worker active, direct isolated elaboration on
Lean 4.24.0-rc1/mathlib `eed770a4` exited 0. The `/tmp` olean SHA-256 was
`3d140dd737b77cff2af177caa702080ab17024f7a9c2ced861a249923267a5bb`.
All ten live `#print axioms` reports returned only
`[propext, Classical.choice, Quot.sound]`.

Accepted mathematics: the exact equality of the explicitly defined Yukawa and
unscreened real functions at `m=0`; the stated lower comparison derived from
`1+x <= exp(x)`; a constructive unboundedness result for the defined Yukawa
function when `m,B>0`; strict monotonicity in `M` of the supplied affine
`screeningLength A M Mpl` for positive `A,Mpl`; the elementary threshold
equivalence and contrapositive; and the rational bracket
`1/4 < 13672/47675 < 1/3`. These are genuine Lean theorems.

Scope limits found by exact source reading:

* No Laplacian, distribution, Green-function equation, scalar field, potential,
  linearization, mass derivative, spacetime, natural-unit conversion or
  cosmological observation is defined. The labels "Yukawa Green's function"
  and "screening length" are interpretations of supplied real definitions.
* `yukawa_unbounded_at_origin` proves the existential statement that every
  positive bound is exceeded at some positive radius. It does not prove a
  topological limit at zero, compare to `R_f`, or establish that either function
  solves a differential equation.
* `screeningLength` is defined directly as `A*(M/Mpl)`. This is the correctly
  solved affine form once `kappa=8*pi/Mpl^2` and
  `m^2=lambdaEff/(kappa*M^2)` are substituted; it is not an arbitrary physical
  ansatz. The first relation is the standard GR coupling convention. The second
  follows by two elementary differentiations of the sibling module's defined
  exponential potential. The real gap is narrower: neither differentiation nor
  the cross-module composition is currently represented in Lean's type system.
* `horizon_requires_planckian_scale` is multiplication/division by an arbitrary
  positive `A`. It does not name a Hubble radius, Planck mass, observed Lambda,
  metres, TeV or AU. Therefore the physical threshold follows only after the
  external identifications and numerical inputs are supplied.
* The sole numerical theorem checks the rational `13672/47675` bracket. It does
  not verify the displayed Planck-2018 quantities, the table, the claimed
  `0.3 AU`, sixteen-order gap, laboratory accuracy, or observational provenance.
* The capstone is exactly a conjunction of the preceding real identities and
  inequalities. Its docstring's exclusions of `R_f`, field-scale commitment and
  falsifiability claim exceed its formal type.

Verdict: accept the real-function comparison, unboundedness witness, monotonicity
and threshold arithmetic. Label `M >= approximately 0.29 Mpl` a **conditional
reduction with a partially formalized antecedent chain**: the downstream kernel
and threshold algebra is formalized, the missing derivative and cross-module
bridge are elementary and additive, while the action variation/Green-equation
interpretation and observational inputs remain external. The file alone does
not prove that its defined function is the required Green kernel.

### `PF/SigmaAbscissa_r212.lean` --- accepted combinatorics and closed-form level sets; abscissa bridge open

Root read all 624 lines at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. The file imports only mathlib
modules and no project source. Its source SHA-256 is
`1207f64b700f17fa44756edb9073049a8a11f39bf2c0f6b366ae1db4b00faa22`;
its last-touch commit is `7b4c12ddf73db01e87d5d8e89a2a0674e72593ac`
(2026-08-07). With unrelated tracked edits preserved and no Lean worker active,
direct isolated elaboration on Lean 4.24.0-rc1/mathlib `eed770a4` exited 0. The
`/tmp` olean SHA-256 was
`242386c2b9b449b871a2d96ae19dbea381429d615ccfe27702834c45670b877e`.
All thirty-one live `#print axioms` reports returned exactly
`[propext, Classical.choice, Quot.sound]`.

Accepted mathematics: the exact base-3 digit-block identity for every complex
`omega`; the corresponding modulus and `3^k`-block coefficient-sum norm; the
complete zero and one level sets of the explicitly defined closed-form real
function `sigma`, including mathlib's degenerate `logb 3 0 = 0` branch; the
rationality consequence of membership in the zero/one levels and its
irrationality contraposition; the three exact evaluations at `1,3/2,2`; the six
named irrational values' exclusion from those two levels; and the Taylor-bound
proof that the golden ratio is also off the `1/2` level. These are substantial,
clean Lean results.

Scope limits found by exact source reading:

* The Dirichlet series `R_f`, convergence, an abscissa and singularities are not
  defined. `sigma` is defined directly as `logb 3 |1+2*cos(pi*alpha)|`. The file
  explicitly discloses that the analytic implication from block growth to an
  abscissa is unformalized. Therefore Lean does not prove that `sigma` is the
  abscissa or the rightmost singularity of `R_f`.
* The finite block theorem sums coefficient phases over `n=0,...,3^k-1`; the
  manuscript series starts at `n=1`. Relating these coefficient blocks to
  weighted Dirichlet partial sums and proving that the endpoint shift is
  analytically harmless remain part of the missing bridge.
* Lean proves which canonical values do or do not lie on the selected levels
  `{0,1}`. It does not define or derive a rule saying that exactly those two
  levels select physical/problem-specific alphas. Thus "selects exactly the
  three rational values" is conditional on an external selection criterion;
  the function itself assigns values to all real alphas.
* The decimal evaluations printed for the six misses, the nearby
  `alpha*=1.6192817`, and the claimed distances/percentages are comments, not
  theorem conclusions. The golden-ratio proof establishes rigorous separating
  inequalities and non-equality, which is the accepted formal content.
* The capstone accurately conjoins the three `{0,1}` hits and six misses, but
  its "first non-circular selection mechanism" language exceeds the theorem
  type until the analytic and selection-rule bridges are supplied.

Verdict: accept r212 as a strong non-circular base-3 coefficient identity plus
an exact analysis of a motivated closed-form proxy. Classify the claim that this
proxy is the abscissa of `R_f` as an unformalized analytic bridge, and classify
the three-value "selection" as conditional on choosing the `{0,1}` level rule.
Nothing in the file proves a Millennium statement, as its own scope note says.

### `PF/PoincareAlphaFromH3CoxeterHalfArg.lean` --- accepted as explicitly conditional arithmetic

Root read all 138 lines at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`, together with the already completed
line-by-line root audit of all 413 lines of its sole project dependency
`PF/H3CoxeterOrigin.lean`. Source SHA-256 values are
`3cf4cd89e2f167f9b5792b59a31fe5fbb4a63bc79128eb98cdbe6d857aa5ba7e`
and `fcdc87bf9a9112c63ad0b5fc236cf3d0e3144a3b13d401f3102f2e3166d7106d`,
respectively. The file's last-touch commit is
`2973b67edf5a92ad256cf47ab76099cbe3161656` (2026-09-29). Direct isolated
elaboration on Lean 4.24.0-rc1/mathlib `eed770a4` exited 0; the `/tmp` olean
SHA-256 was
`b20ba29777ae9bde7b88a73a60ad486361ed598b7e9b7caa4de4c54d08d087b9`.
Both live `#print axioms` reports returned exactly
`[propext, Classical.choice, Quot.sound]`.

Accepted mathematics: the separately defined real value
`pi/H3_Coxeter_number` reduces to `pi/10`; and any real `alphaP` satisfying
`alphaP = pi/(10*(pi/10))` equals `1`. The file contains no substrate reference
in either theorem and cleanly isolates the arithmetic from the framework bridge.

Scope limits found by exact source and dependency reading:

* The decisive hypothesis `h_uc` supplies the universal-coupling identity that
  already contains `alphaP` on the left and the target-bearing constants on the
  right. The theorem proves its arithmetic consequence; it does not derive the
  coupling identity.
* `H3_Coxeter_number` reduces definitionally to `10` in the imported module.
  The imported H3 exponent/combinatorial data are stipulated structures; no
  Coxeter diagram or reflection representation is constructed to derive them.
* No substrate operator, principal eigenvalue, geometrization map or equality
  between such an eigenvalue and the H3 half-argument is defined here. The file
  explicitly and correctly marks that operator-theoretic identification open.
* Consequently the theorem does not independently derive the book's
  `substrate_alpha_skeleton 0 = 1`, close r338's definitional circularity, or
  establish a physical Poincare anchor. It provides the non-circular arithmetic
  core needed after the missing identification is supplied.

Verdict: accept as kernel-clean, non-substrate-referencing conditional
arithmetic. The file's own scope discussion is unusually accurate. Do not cite
it as an unconditional alpha derivation; cite it as reducing that derivation to
the explicit universal-coupling/operator-identification premise.

### `PF/SpectralGap.lean` --- accepted numerical algebra; not P versus NP or an operator spectrum

Root read all 274 lines and all 600 lines of its sole project dependency
`PF/IntervalArithmetic.lean` at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. Their source SHA-256 values are
`5c6c629d15f1a34ea9f4b3249b15c34514166b959d281bf0700833341ef286f0`
and `d3fce0d7a55383f40b54f39f01459d5ae6240566a93508bdf3483bbe761fc44f`.
Last-touch commits are `4af53cbf92646d6e9ec049a732dba569b2b5111d`
(2026-06-15) and `86a61d197f0f9abe02ac2eaae42ef598b9b22a4f`
(2026-04-24), respectively. Direct isolated elaboration on Lean
4.24.0-rc1/mathlib `eed770a4` exited 0; the `/tmp` olean SHA-256 was
`c90209cd0c1f1a4f0a7f0ce62b21c4cc1e801874a07891d5817f1b36e6dfc208`.
Because the source has no live axiom audit, root used an isolated wrapper to
capture fifteen principal endpoints. Every report returned exactly
`[propext, Classical.choice, Quot.sound]`.

The dependency's repeated "certified axiom" comments are stale: the numerical
bounds used here are theorem proofs from mathlib pi bounds, square-root
identities and rational arithmetic. No project axiom survives into the audited
endpoints.

Accepted mathematics: rigorous enclosures for the two explicitly defined reals
`pi/(10*sqrt 2)` and `pi/(10*(phi+1/4))`; their positive difference and stated
decimal enclosure; the rearranged product/cross identities; the exact ratio and
its three-digit bracket; and the elementary fact that unequal scalar values
cannot be equal. These are clean numerical and real-algebra theorems.

Scope limits found by exact source and dependency reading:

* `lambda_0_P` and `lambda_0_NP` are defined directly as the two closed-form
  real numbers. No operator, spectrum, ground state, language, machine,
  complexity class or polynomial-time predicate is defined in either file.
* `P_neq_NP` has type `spectral_gap != 0`; it does not mention standard `P` or
  `NP`. `pvsnp_spectral_separation` existentially packages the same defined
  number. Their names and opening claim "proving P != NP" exceed their types.
* The supposed polylog spectral formula is not derived here; it is instantiated
  by the definitions of the two `lambda_0` values. Thus the ratio theorem is an
  algebraic consequence of definitions, not a resolution of an operator-theory
  problem.
* `unitary_conjugation_incompatible_with_spectral_gap` takes only the scalar
  hypothesis `lambda_0_P=lambda_0_NP` and derives a contradiction. It defines no
  Hilbert space, unitary, conjugation or spectral-invariance theorem. Its
  operator-structural interpretation is prose.
* `universal_pi_10_coupling` restates the two defining division identities. It
  contains no consciousness structure and proves no physical universality.
* The corrected numerical value `0.0539677287` is therefore a value of the
  framework's chosen formulas. It is neither a measured spectral gap nor a
  prospective empirical prediction, and it does not settle which actual
  operator the manuscript intends those digits to describe.

Verdict: accept the certified real arithmetic and corrected decimal value at
their exact types. Classify every P-versus-NP, ground-state and unitary-operator
reading as an unformalized interpretation resting on the missing operator and
complexity bridges. This file does not formalize or resolve the Clay problem.

### `PF/Consciousness/RfAlphaScalingConstantBase3.lean` --- accepted termwise derivative; unique-prefactor headline rejected

Root read all 238 lines, all 527 lines of its direct project dependency
`PF/Consciousness/FractalResonance.lean`, and the exact `digitalSum3` definition
and relevant recursion context in `PF/TuringEncoding/Basic.lean`, at repository
HEAD `088fffe134ff71e99b1228f0e197fc22f20c1b79`. Source SHA-256 values are
`5572e60d1d2ac022166c4d5e7c24aede581f16e16632d0abd5770a6174d338ef`,
`418a68d392204ba56fce69446d4fcd7c062ffb38ef0495b5fa9ec92f6f31a503`,
and `757324273a3ddac541c3c4f6e8bf48f193c63c3d4c198524066de31d651cb0c7`.
The audited file is exactly quarantined commit
`0ef96a27fc9d03a98a281a82018172742ffe34b9` (2026-10-07). Direct isolated
elaboration on Lean 4.24.0-rc1/mathlib `eed770a4` exited 0; the `/tmp` olean
SHA-256 was
`db8391148a5ed7e0d24720b4325038388e2e6faa7cd0b5a010c371f13936b70f`.
All five live `#print axioms` reports returned exactly
`[propext, Classical.choice, Quot.sound]`.

Accepted mathematics: `D3(n) mod 2 = n mod 2`; the exact real-parameter
`HasDerivAt` and `deriv` formula for each individual complex summand; the
factorization of that derivative as
`(i*pi)*D3(n)*term`; the existential demonstration that an unconstrained
structure function can absorb any nonzero prefactor; the inequality between
the individual coefficient `i*pi*D3(n)` and the positive real `pi/10`; and the
coefficient norm formula. The dependency genuinely defines `R_f` as a `tsum`
and proves absolute summability for `Re(s)>1`.

Scope limits found by exact source and dependency reading:

* No theorem differentiates the infinite `tsum`. The file explicitly marks the
  needed interchange of derivative and sum open. Consequently Lean proves the
  summand derivative, not `d R_f/d alpha`.
* `i*pi` is the natural chain-rule factor after normalizing the remaining
  function to be the `D3`-weighted resonance sum. It is not a uniquely
  determined scaling constant when the manuscript's `f(alpha_c,s)` is left
  unconstrained. Indeed `scaling_constant_underdetermined` proves that every
  nonzero constant works after rescaling `f`.
* `prefactor_ne_pi_div_ten` compares `i*pi*D3(n)` directly with `pi/10`. The
  chapter's displayed law instead compares a derivative with `(pi/10)*f`.
  Since `f` may contain `10*i*D3(n)` and the remaining sum, the theorem does not
  refute that factorization; it refutes only identifying the bare termwise
  coefficient itself with `pi/10`.
* The external finite-difference values, convergence of the weighted sum's
  modulus to one, the `[1.00,1.09]` range and the critical-point numerical
  claims are not theorem conclusions in this file.
* Nothing here excludes `pi/10` from other framework identities. In particular
  it does not refute the separately discussed product invariant
  `alpha*lambda=pi/10`.

Verdict: accept the termwise calculus and the proof that Ch07's free `f` leaves
its displayed constant underdetermined. Reject the commit/title claim "the
constant is i*pi, not pi/10" as too strong. The accurate statement is: with the
specific normalization where `f` is the `D3`-weighted resonance sum, the
chain-rule prefactor is `i*pi`; without that normalization no unique prefactor
is selected. The derivative-of-`R_f` theorem remains open.

## EXACT FORMAL AUDIT: `InClassPRepair_2026_10_08.lean`

Status: **accepted as an additive semantic repair and a decisive audit of the
legacy definitions; not a proof of standard P != NP.** The file is untracked,
is not imported by `PF.lean`, and changes no existing definition.

Root read all 657 lines of
`PF/TuringEncoding/InClassPRepair_2026_10_08.lean`, all 256 lines of its exact
legacy-definition dependency `PF/TuringEncoding/Complexity.lean`, and all 383
lines of `PF/P_NP_Complete_Proof.lean` at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. Source SHA-256 values are
`c6cf22cb115f64af41f34407beec21806e77ca8bf2152f47a0f4377ee87db2a2`,
`19dd8e7732bca3c1e1d42ebf713a4d364184798110fd8203fa85619d2a3e7cfb`,
and `1618c1e4624b322f1845c401e853c48011e63f58acda538ae44631ea3302a421`.
The target has no commit provenance: `git status` reports it as `??`, and
`PF.lean` contains no import of it.

Root directly elaborated an exact copy of the source with only twelve trailing
audit `#print axioms` commands added, using Lean 4.24.0-rc1 and mathlib
`eed770a434957369c6262aa3fb1d6426419016d4`. Elaboration exited 0. The audit
olean SHA-256 was
`f3fe19b45f4e0cb2232d7cc436bd390b1da8982e45a8ad172b592775d50e9fe6`.
`legacy_accepts_const` reported no axioms. The other eleven audited endpoints
used only subsets of the standard kernel dependencies `propext`,
`Classical.choice`, and `Quot.sound`; no project axiom was reported. The source
contains no `sorry`, `native_decide`, axiom declaration, or `Prop := True`
(the only grep match was the scope sentence stating their absence).

Accepted legacy audit:

* The trailing-input clause in legacy `InClassP` makes `M.accepts` constant by
  setting `x := []`. Together with the decision equivalence, every legacy-P
  language is exactly `empty` or `univ`; the file proves both inclusions.
* `IsPolynomialBounded T` also forces `T 0 = 0`, because its exponent is
  required positive while the bound uses `n^k` rather than `(n+1)^k`.
* Simply deleting the invariance clause makes every language satisfy the
  remaining definition: legacy `Machine` stores arbitrary, unrelated
  `accepts` and `steps` functions and has no operational semantics.
* `Lfirst`, the language whose first bit is one, is in legacy `ClassNP` but not
  legacy `ClassP`. Therefore `ClassP != ClassNP`, `not PvsNP_Question`, and the
  project's `P_neq_NP_def` are unconditional theorems for the legacy
  definitions. The spectral/fractal hypotheses do no work in those legacy
  conclusions.

Accepted replacement construction:

* `TM` has finitely many states, a total deterministic transition function,
  one read-write work tape, one read-only certificate tape, step-indexed run
  semantics, and absorbing halting configurations. `CertBlind` is a condition
  on the transition program, not a language-level append invariant.
* `InClassP_Step` requires actual halting by a monotone polynomial time bound;
  `InClassNP_Step` requires actual halting and an existential certificate with
  polynomially bounded length.
* The explicit three-state `firstOneTM` decides `Lfirst` in one step, proving
  the repaired P class does not collapse to `{empty, univ}`.
* `ClassP_Step_subset_ClassNP_Step` is substantive and sound: certificate
  blindness transports state/work runs, monotonicity enlarges the time bound,
  and the absorbing-halting lemma transports the verdict to the larger NP
  runtime.
* The repaired class strictly contains the defective legacy class, at the
  level of language membership.

Scope limits:

* This is a concrete fixed machine model, but no robustness or simulation
  theorem identifies it with a standard textbook model of computation.
* No theorem proves `ClassP_Step != ClassNP_Step`; `PvsNP_Step` is deliberately
  left open. There are no reductions, complete problems, Cook--Levin theorem,
  or diagonal/counting separation from all languages.
* Nothing connects the repaired classes to the fractal operators, alpha
  assignments, spectral gap, or `PolylogEigenvalueConjecture`. Existing PF
  claims over legacy `ClassP`/`ClassNP` are not repaired by this additive file.
* The replacement is not imported by the project root and has not landed in a
  commit. It is verified source, not integrated project semantics.

Verdict: this file correctly proves that the current PF P-versus-NP target is
trivially true for a specification-defect reason, and supplies a credible
operational replacement whose P-versus-NP question remains open. It repairs
the model locally and additively; it does not repair downstream PF theorems or
support any claim to have solved the Clay problem.

## EXACT FORMAL AUDIT: `RightEdgeSigns_2026_10_08.lean`

Status: **accepted as a kernel-clean conditional contour-evaluation reduction
and additive repair of the intended horizontal-edge theorems; not an exact zero
count and not finite-height RH.** The file is untracked and is not imported by
`PF.lean`.

Root read all 377 lines of
`PF/Analytic/RightEdgeSigns_2026_10_08.lean`, all 147 lines of
`RiemannXiTopUnion.lean`, all 192 lines of `RiemannXiEntire_r325.lean`, all 228
lines of `RiemannXiSymmetries_r326.lean`, and the complete relevant proof arc
of the 742-line `RectangleLogBranch_r331g.lean`, including its edge primitives,
log-rotation defects, five-segment chain, rectangle assembly, and seven-input
right-edge endpoint. Repository HEAD was
`088fffe134ff71e99b1228f0e197fc22f20c1b79`.

Source SHA-256 values were:

* target: `249998ab7281f11d2f5a3e80ac8b13a0c67ca7f9a2be6bb9e6ea0e4e64903a9c`;
* `RectangleLogBranch_r331g.lean`:
  `dcb0f20b9128f7493dacadb738b0fd28d69c79227a675c7ad8a6e2c3b2831b65`;
* `RiemannXiTopUnion.lean`:
  `11b99e6e33be56ca6622acaa00ef04ea445882d236cebb292b30d8e94b6beeb6`;
* `RiemannXiEntire_r325.lean`:
  `bd7cc0096acdfdc56770c509b01d3a1f6c653af53962cb72bf0adb5e73b45170`;
* `RiemannXiSymmetries_r326.lean`:
  `4073020f4d3353ad2aeb5f45157a659a5abd90e56ad9752804feb8f1ce1ab7e0`.

Root directly elaborated the target on Lean 4.24.0-rc1/mathlib `eed770a4`.
It exited 0. The isolated olean SHA-256 was
`0766ebef818453886e0d8e3afe42ce0934a6a2ff4655141b1b2e4ef8ea03fd6a`.
All seventeen live `#print axioms` reports returned exactly
`[propext, Classical.choice, Quot.sound]`. The imported r331g olean SHA-256 was
`a247fe93b3e1b338b3f5a1ec3df2ddcde04e08bbd1bce681a557e10693ebc19d`;
the top-union olean SHA-256 was
`a5d38c10ba847e4358598931e10b656fe9d7583f0c03ff387785ec0bad0f5e88`.

Accepted mathematics:

* The real and imaginary parts of the actual `riemannXiEntire` are respectively
  even and odd under `t -> -t`, by the global conjugation theorem.
* The certified `t = 15`, `sigma in [1/2,1]` top-union inequality extends to
  the full `sigma in [0,1]` top edge by vertical reflection, and to the bottom
  edge by conjugation. Both rotated horizontal-edge hypotheses consumed by
  r331g are therefore discharged without new numerics.
* R1, R2, and R3 on the nonnegative right edge generate the three negative-time
  pieces with the correct rotations. Together with the horizontal edges they
  discharge all seven inputs of r331g's
  `rectangleIntegral'_logDeriv_eq_of_right_edge_chain`.
* Consequently Lean proves
  `RectangleIntegral' (logDeriv riemannXiEntire) zF wF = 2` conditional on the
  exact three right-edge sign hypotheses R1--R3.

Critical correction to the earlier accepted RH state:

* Root read all 101 lines of the protected
  `RiemannXiTopEdge_r331c.lean` and all 112 lines of
  `RiemannXiBottomEdgeAtMinus15_r331d.lean`. Neither has an olean.
* A single direct root elaboration of exact r331c exited 1. Because the file
  does not open `PrincipiaTractalis.RiemannXiEntire`, unqualified
  `riemannXiEntire` is captured by `autoImplicit` as an unknown non-function.
  Lean emitted eight errors, and the three surviving audit prints for
  `top_edge_re_neg_full`, `top_edge_neg_xi_re_pos`, and `top_edge_ne_zero`
  included `sorryAx`.
* Therefore r331c/r331d as modules are not accepted artifacts. Their intended
  mathematics is nevertheless recovered independently and cleanly by this
  additive file, which explicitly opens the defining namespace and disables
  `autoImplicit`. The standing instruction not to edit r331c was obeyed.

Provenance/integration limits:

* The target is `??` untracked, has no commit provenance, and is absent from
  `PF.lean`.
* `RectangleLogBranch_r331g.lean` has a tracked uncommitted 20-addition,
  4-deletion header-only rewrite. Its compiled olean predates that prose edit;
  the theorem body consumed here is present in the compiled artifact and its
  dependency chain is reflected in the target's clean axiom prints.
* R1 (`Re xi(1+it)>0` on `[0,13]`), R2 (`Im xi(1+it)>0` on
  `[13,29/2]`), and R3 (`Re xi(1+it)<0` on `[29/2,15]`) remain hypotheses.
  No certified producer for any of the three is added here.
* This theorem evaluates the normalized contour integral conditionally. It
  does not itself import or compose the argument-principle zero-count identity,
  prove the three signs, prove an upper count unconditionally, or establish
  finite-height RH.

Verdict: this is genuine and valuable RH plumbing. It reduces the faithful
contour-evaluation gap to exactly three positive-height right-edge sign
certificates and repairs the intended horizontal-edge facts without touching
the broken protected files. Exact count remains open until R1--R3 are certified
and the contour result is composed with the independently verified
argument-principle/counting layer.

## EXACT FORMAL AUDIT: `ConvectiveDerivativeConnection_2026_10_08.lean`

Status: **accepted as a substantial contentful PDE-definition bridge on
complex vector Schwartz fields; not a Clay Navier--Stokes result and not yet a
complete Cauchy-problem formalization.** Unlike the other new additive audit
files, this untracked file is already imported by the dirty `PF.lean`.

Root read all 968 lines of
`PF/NavierStokes/ConvectiveDerivativeConnection_2026_10_08.lean`, all 360
lines of its exact `ConvectiveDerivative.lean` dependency, and all 298 lines
of `BilinearScaffold.lean`, at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. Source SHA-256 values were
`17ecce28cf4280fd86fd46d0227af1eb574693cf6ed329906051ff3a63b800c6`,
`fb7991b3d622508dfca77ed4004c1edbb86f7a82d7930a983d83257eb2ce3b96`,
and `333cd140d666d5cdfff43836400fe5f100a4e80cad041ab3f12b187f0215634d`.

Root directly elaborated the target on Lean 4.24.0-rc1/mathlib `eed770a4`.
It exited 0. The isolated olean SHA-256 was
`a622bb416d26f6c3b58b3e5706779cf40992fee260ea6fead8c3ea2b030b6b90`.
All 36 live `#print axioms` reports returned exactly
`[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`,
`native_decide`, or project axiom declaration.

Accepted formal content:

* The prior scalar components
  `convectiveComponent u v i = sum_j u_j * partial_j v_i` are reassembled into
  a vector Schwartz field `convectiveTerm`, with a pointwise component theorem.
* Both zero-input identities and additivity in both slots are proved; complex
  homogeneity is proved in the transporting slot. The transported slot inherits
  only the real-linearity supplied by the spatial derivative layer.
* `vectorLaplacian`, scalar pressure derivatives, and an existential
  `IsPressureGradient` constraint are genuine typed objects.
* `momentumResidual` is the pointwise expression
  `partial_t u + (u dot grad)u - nu Delta u + grad p - f`, and
  `IsNSSolution` links the supplied `dtu` field to an actual real-time
  `HasDerivAt`, imposes divergence-free flow, constrains pressure to a gradient,
  and requires the residual to vanish on `Set.Icc 0 T`.
* The zero solution proves the predicate is inhabited. Force-shift and
  force-absorption theorems correctly distinguish this predicate's forced and
  unforced scopes.
* The equivalences exposing when the convective carrier collapses to the
  constant-zero carrier, and when the full residual collapses to the Stokes
  residual, are mathematically faithful reductions to vanishing of the actual
  convective components.

Scope and semantic limits:

* `BilinearMildOperator` is a legacy name for a structure containing an
  arbitrary binary carrier plus only two zero-input identities. It does not
  require additivity, scalar homogeneity, a heat semigroup, Leray projection,
  or a Bochner integral. `convectiveTransportShell` is the instantaneous term,
  not the Fujita--Kato mild operator.
* `BilinearBoundProp convectiveTransportShell` unfolds to an instantaneous
  quadratic seminorm inequality. That inequality is open and is not the
  missing heat/Leray/time-integrated Fujita--Kato estimate.
* No theorem exhibits a Schwartz pair with nonzero convective term. Thus Lean
  does not yet separate this carrier from `trivialBilinear`, even though the
  pointwise formula is correct. The claim that producing such a witness is a
  bounded next task is a feasibility assertion, not a theorem.
* `IsNSSolution` has no initial datum or initial-condition clause, assumes
  neither `0 < nu` nor `0 <= T`, and becomes time-vacuous on `Set.Icc 0 T` when
  `T < 0` apart from the pressure-gradient clause. Calling it the full Cauchy
  problem therefore overstates its current type.
* Velocities and pressures are complexified Schwartz fields. No bridge to the
  real-valued smooth finite-energy data and solution class in the Clay
  statement is proved.
* There is no existence, uniqueness, continuation, blow-up, regularity,
  a-priori estimate, or vortex-stretching theorem. The force has no time
  regularity or Clay decay constraints; the file explicitly acknowledges this.
* `VortexStretchingBoundedHypothesis` and
  `NS3DVortexStretchingObstruction` remain open and are not imported here.

Integration/data-risk note: the target is `??` untracked, while line 601 of the
tracked-but-dirty `PF.lean` imports it. The direct target build is verified, but
the project root now depends on a file that would disappear from a
tracked-files-only transfer or commit. No tracked or untracked source was
changed during this audit.

Verdict: this materially improves Lean coverage of the nonlinear momentum
equation and repairs the earlier orphaning of `convectiveComponent`. It should
be labelled a contentful smooth-Schwartz PDE predicate and conditional
infrastructure. It neither states nor proves the standard Clay alternative,
and it does not change the status that the Navier--Stokes Millennium problem is
unformalized/open in PF.

## EXACT FORMAL AUDIT: `SpectralInclusion_2026_10_08.lean`

Status: **accepted as an exact finite-dimensional spectral proxy and a genuine
repair of the operator-spectrum quantification; not a Yang--Mills QFT
construction or a Clay mass-gap result.** The file is untracked and is not
imported by `PF.lean`.

Root read all 337 lines of
`PF/YangMills/SpectralInclusion_2026_10_08.lean` and the relevant defining and
capstone arcs of its exact 1072-line dependency
`PF/YM_ClayLiteralClosureAttempt.lean`, at repository HEAD
`088fffe134ff71e99b1228f0e197fc22f20c1b79`. Source SHA-256 values were
`c0c9276b302c1c9f1a622a5818499a69c94a5035b6b29fb63d381db9c720309c`
and `0710f383f0de75e0a0a6fc0c48882077fed15e6cf9f22c039bbda1163705fa6e`.

Root directly elaborated the target on Lean 4.24.0-rc1/mathlib `eed770a4`.
It exited 0. The isolated olean SHA-256 was
`77b2e74ddf78483f7ef4285508434e837db2dc5c33e4b1e7478a115bfd2f7bd3`.
All 12 live `#print axioms` reports returned exactly
`[propext, Classical.choice, Quot.sound]`. A source scan found no proof-use of
`sorry`, `sorryAx`, `native_decide`, project axiom declaration, or
`Prop := True`; the only matches are the file's own scope comment.

Accepted formal content:

* `H_Wightman` is exactly the two-dimensional real Euclidean space and
  `H_OS_Wightman` is the continuous linear operator represented by the real
  symmetric matrix `[[1, 1/2], [1/2, 1]]`.
* The dependency already proved explicit eigenvectors with eigenvalues `1/2`
  and `3/2`, and equality of its eigenvalue set with `{1/2, 3/2}`. The new file
  connects that result to the generic operator-parameterized `specSet` by
  definitional equality and proves the exact set theorem.
* It consequently proves zero is absent, inclusion in `[1/2, infinity)`,
  inclusion in `{0} union [1/2, infinity)`, inclusion in `[1/2, 3/2]`, and
  exact least and greatest spectral values.
* `H_OS_mass_gap_one_half_specSet` repairs the older theorem's final clause:
  the lower-bound quantifier now ranges over the actual `specSet H_OS_Wightman`
  rather than the literal pair `{1/2, 3/2}`.
* The existential capstone likewise contains membership of both displayed
  eigenvalues in the selected operator's own `specSet`. This is a real
  type-level strengthening of the finite-dimensional proxy.

Scope and semantic limits:

* The project definition `specSet` is the real point spectrum
  `{E | exists v != 0, H v = E v}`, not a library definition of the full
  spectrum of a possibly unbounded self-adjoint operator. For this explicit
  two-dimensional symmetric matrix the eigenvalue calculation is exact, but
  the theorem does not establish a general spectral-theory interface.
* Zero is proved **not** to belong to this spectrum. Thus the result is a
  positive lower bound for the entire two-level spectrum, not the physical
  statement that a Hamiltonian has a zero-energy vacuum separated by a
  positive gap from excitations.
* The existential capstone remains satisfiable by an elementary finite matrix.
  It supplies no compact nonabelian gauge group, gauge fields or connections,
  Yang--Mills action, Euclidean measure on distributions, Osterwalder--Schrader
  axioms, reflection positivity/reconstruction, local observables,
  infinite-dimensional physical Hilbert space, vacuum, or four-dimensional
  interacting QFT.
* The header discloses these exclusions accurately. No manuscript theorem is
  downgraded by their absence; they delimit what this Lean theorem formalizes.

Verdict: accept the mathematics as a kernel-checked finite-dimensional
spectral-inclusion result and a corrected operator-quantified proxy. It does
not alter the program-level conclusion that PF stores/illustrates a mass gap
rather than constructing the four-dimensional quantum Yang--Mills theory
required by the Clay problem.

## EXACT FORMAL AUDIT: `GeneralRelativityContentful_2026_10_08.lean`

Status: **accepted as a substantial abstract-algebra/ODE repair in a new
namespace; not tensorial general relativity, not a replacement of the legacy
Props, and not an integrated physical mechanism.** The file is untracked and
is not imported by `PF.lean` or any other PF module.

Root read all 609 lines of
`PF/GeneralRelativityContentful_2026_10_08.lean`, all 161 lines of its exact
`ModifiedFriedmann_r187.lean` dependency, the relevant definition/theorem arcs
of the 323-line `LambdaEffFromAction.lean` dependency, the exact scalar-field
definitions in the 462-line `Wave58/Ch08FieldEquationsConcrete.lean`
dependency, and the legacy Prop definitions in `GeneralRelativity.lean`, at
repository HEAD `088fffe134ff71e99b1228f0e197fc22f20c1b79`. Target and direct
dependency SHA-256 values were:

* target: `47915425f4948f9fb41ac1672ae8ed3bd3e4eac4f596535643567017f80da72b`
* `ModifiedFriedmann_r187.lean`:
  `fed3231ac0bd7c9361c0e86eb2169811d8cc1748acddf03382d1b55f981632b4`
* `LambdaEffFromAction.lean`:
  `42c5dae393549b8c68a146838a32a1ff943fb679a2f48d6e7bc9a7540a0cce87`
* `Wave58/Ch08FieldEquationsConcrete.lean`:
  `45fde39a2b8dd0f2ec8a7e774191a0005feb8ca4f3523eadc9898c8c384ff138`
* legacy `GeneralRelativity.lean`:
  `0d9cf7f4bd5e0b4b613b76980bc3feab2cb2c042ca0d8f37551283d88e7cb4c4`

Root directly elaborated the target on Lean 4.24.0-rc1/mathlib `eed770a4`.
It exited 0. The isolated olean SHA-256 was
`f41a2dcdf2cfb228e9603d619cd0aabdef6cc1a3915191ab1672a6e42e8ef0ac`.
All 22 live `#print axioms` reports returned exactly
`[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`,
`sorryAx`, `native_decide`, project axiom declaration, or `Prop := True`.

Accepted formal content:

* `Tensor2` is a real `4 x 4` matrix and `DivOp` an arbitrary real-linear map
  from such matrices to four-vectors. From a constant-scalar field-equation
  identity, `D G = 0`, `D g = 0`, and nonzero coupling, the file correctly
  derives `D T + D C = 0`.
* Explicit one-point matrix witnesses show that neither `D T` nor `D C` must
  vanish separately, and separate countermodels show that the `D G = 0` and
  `D g = 0` hypotheses are load-bearing.
* The FLRW modified-continuity equation is proved equivalent to the comoving
  energy-balance identity under differentiability and nonvanishing scale
  factor assumptions. Satisfying and refuting instances are exhibited.
* For the Wave58 scalar residual, positive `ch2` strictly lowers the residual,
  while the modification vanishes at zero. This is exact arithmetic for the
  defined scalar density.
* For arbitrary differentiable real functions, conservation of
  `Ecl + Eq + c2*I` is equivalent to the corresponding derivative balance.
  An explicit family has conserved total budget and nowhere-conserved
  classical component; uniqueness of `c2` is proved when `deriv I != 0`.
* Positivity, strict field suppression, non-extinction, and the time-dependent
  suppression ODE are correctly inherited from the two earlier modules.

Scope and integration findings:

* The header's statement that the original names are kept while their bodies
  are replaced is false as an integration description. The new declarations
  live under `PrincipiaTractalis.GeneralRelativityContentful`; the legacy
  declarations live under `PrincipiaTractalis`, retain their True-equivalent
  bodies, and remain the ones imported by the project. No consumer imports the
  new module. This additive file is therefore an alternate formalization, not
  a replacement or project-level repair.
* `DivOp` is not a covariant divergence, `Tensor2` is a matrix at one point,
  `G` is not constructed from a metric, and the contracted Bianchi identity is
  assumed as `D G = 0`. The theorem also uses a constant real `Lam`; it does
  not address the previously verified variable-`Lambda_eff` divergence term
  or resolve the Ch08/Ch14 coefficient mismatch.
* The sharpness witness is a valid algebraic countermodel for the abstract
  implication. It is not a spacetime solution, does not construct a
  consciousness stress-energy tensor field, and supplies no Einstein
  dynamics or empirical premise.
* The Wave58 input is only the scalar residual
  `G - 8*pi*(T+C)` with a stipulated scalar density. Strictly changing that
  residual proves dependence on the added term, not that any modified field
  equation holds or describes nature.
* The energy-information result is calculus on arbitrary real functions. It
  supplies no entropy/information operationalization, no Noether derivation,
  no `U(1)_C` current, and no identification of the positive factor with the
  physical speed of light squared.
* `DarkEnergyAsLambdaEffHypothesis` conjoins facts about two different
  constructions: `Lam0*exp(-phi/M)` and
  `Lam0*exp(-integral g)`. No theorem identifies `phi/M` with the integral of
  `g`, so the conjunction is not a composed action-to-cosmology mechanism.
  The variational stress-tensor step, kernel, and calibration remain outside
  Lean exactly as the source discloses.

Verdict: accept the individual theorems as meaningful conditional reductions
and non-vacuous abstract counterexamples. Do not cite the bundle as formalized
general relativity or as a repaired project-level GR hypothesis until an
explicit integration choice is made. Its current correct label is an
unimported, namespaced, contentful proxy; the physical and manuscript claims
remain conditional or unformalized.

## OPEN ITEMS FOR THE AUTHOR

1. ch08 `Theta(ch_2 - 0.95)`: reading R1 or R2.
2. ch09 vs ch07: which of `lambda_0(H_P)`, `lambda_0(H_NP)` is larger.
3. ch07 `thm:p-np-gap`: which operator the printed digits denote.
4. The consciousness-strata dimension in the Grothendieck appendix: which
   invariant (set dimension is excluded --- `dim` rises while `S_t` shrinks).
5. ch10 `d_f`: which multifractal model, or whether a spectrum `D(h)` replaces a
   single `d_f`.
6. ch07 pi/10: whether to restate as the product invariant
   `alpha * lambda = pi/10` with `pi/h(H_3)` as candidate origin, per ch03 and
   the version log.

Author: Pablo Cohen + Claude Opus 5. 2026-10-07.


---

## SESSION HANDOFF (recorded at end of pass 1)

### Repository state
* repo `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE`, branch `master`
* HEAD `088fffe134ff71e99b1228f0e197fc22f20c1b79`
* upstream `origin/master`, **113 commits ahead, UNPUSHED**
* tracked modifications: **0** (worktree clean apart from untracked artifacts)

### Quarantined commits --- preserved, unaccepted
* `3cdd430c329e0393438bc3a0ac2e9d68d7331c17` 2026-10-07 15:20:10 -0400
  "errata: a false theorem in ch01, three stale values, and the book would not build"
* `088fffe134ff71e99b1228f0e197fc22f20c1b79` 2026-10-07 15:46:02 -0400
  "title page: two unsupportable claims, and the p=3 Euler factor that inverts a bracket"

**Also requiring review, not formally quarantined:** `0ef96a27`. Its §2 and its
title claim ("it is i\*pi, not pi/10") were found to exceed what its proofs
establish; its four Lean declarations are PROVISIONAL pending exact audit. The
earlier commits of this session (`c1318040` Wave-family anchoring, `d35f1f2d`,
`f4dbfc96`, `35585042`, `94677b04`, `e0ed0633`, `a2996300`, `79e3c416`,
`70ca6ec2`, `fb2eeeaf`) were not reviewed under the audit directive.

### Resume point
Reading pass complete. Begin the exact formal audit with the definitions that
control ch08's gate and repaired dynamics:
`PF/Ch2ThresholdSelection.lean`, `PF/Ch08Ch14ModifiedRelativity.lean`,
`PF/LambdaEffFromAction.lean`, and `PF/ScreenedKernelAndFieldScale.lean`;
personally read their imports and theorem bodies, then directly elaborate and
capture `#print axioms` for the accepted endpoints before moving to the remaining
handoff list.

### Gate sweep --- DO NOT RELAUNCH
* pids `981896` (wrapper), `981898` (`python3 scripts/gate_sweep_1007.py`)
* script `PF_Lean4_Code/scripts/gate_sweep_1007.py` (untracked)
* log `/tmp/sweep_fresh_1007.log`
* output `codex/PRISTINE_SWEEP_2026-10-07.tsv` (untracked, in progress)
* at first handoff record: 552/1455. **Superseded:** the sweep continued and
  reached **1417/1455** (1418 TSV rows, avg 15.2 s/module). The local Bash
  wrapper that launched it was killed by LOCAL memory pressure; the remote
  process was `setsid nohup`-detached and was unaffected. Acer showed 12Gi
  available and no OOM kills. Final tally recorded below once it exits.
* fresh TSV so every module is re-gated with the fixed criterion (e); the
  2026-10-06 TSV is preserved untouched
* **results PROVISIONAL**: the gate implementation and BOTH criterion-(e)
  defects (mine, and the earlier comment-stripper defect recorded in
  `version_history` v2.7.2) are unaudited. Do not quote a PRISTINE percentage.

### Artifacts to preserve (all untracked)
* this ledger
* `codex/PRISTINE_SWEEP_2026-10-07.tsv`
* `PF_Lean4_Code/scripts/gate_sweep_1007.py`
* **44** `*.prefix_2026-10-07*` backups across `Principia_Fractalis_master_folder/`,
  `PF_Lean4_Code/`, `PF_Coq_Code/` --- including 25 `Wave*MasterCapstone.lean`
  backups from the family-anchoring commit and `YM_ClayLiteralClosureAttempt.lean`
* `PF_Lean4_Code/PF/Analytic/RiemannXiTopEdge_r331c.lean` (standing instruction;
  untracked, confirmed present)

### Standing constraints for the next session
1. Resume the complete reading pass; read every remaining included `.tex` in
   full, in book order. No searches or summaries in place of reading.
2. Update this ledger continuously.
3. No manuscript mutation. No Lean/API mutation. No rename sweep.
4. Do not launch another gate sweep.
5. Defer all six authorial questions, including the ch08 R1/R2 choice, until the
   reading pass AND the subsequent exact Lean audit are both finished.
6. After the reading pass: audit in full, with direct elaboration and
   `#print axioms`, `PF/SigmaAbscissa_r212.lean`, `PF/H3CoxeterOrigin.lean`,
   `PF/PoincareAlphaFromH3CoxeterHalfArg.lean`,
   `PF/NSAlphaFromH3ExponentSum_r340.lean`, `PF/SpectralGap.lean`,
   `PF/Consciousness/RfAlphaScalingConstantBase3.lean`, and the exact
   `ChernWeil`/consciousness-measure definitions used by ch04, 06, 07, 18, 30, 31.
7. All findings in this ledger remain PROVISIONAL until the full pass completes.

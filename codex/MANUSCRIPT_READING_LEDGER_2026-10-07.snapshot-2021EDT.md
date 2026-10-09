# Manuscript reading ledger --- audit pass of 2026-10-07

Commit at start of pass: `0ef96a27`. Commit now: `088fffe1`.
Toolchain: Lean 4.24.0-rc1 / Lake 5.0.0 / mathlib `eed770a4` / Rocq 9.1.0.
Include graph: **68 files, 38,995 lines at commit `088fffe1`** (resolved
recursively from `main.tex`, comment-aware). The 7 `.tex` on disk not reached by
the graph are 2-line stubs.

*Denominator note.* The graph measured **38,923** lines at commit `0ef96a27`,
before the two quarantined commits; those added 72 lines. Any percentage must be
stated against its commit.

Status: **PASS INCOMPLETE.** **24,850 of 38,995 lines read in full (63.7%)**
across 43 of 68 files; `ch08` additionally read in part. An earlier draft of this
ledger said "~12,900 (33%)" --- that was an estimate that counted the `ch08`
partial as full, and is corrected here. Halted on context budget, not on a
decision. Pass 2 resumed from the recorded boundary and completed ch11--ch28.
The continuing controlled lane has now completed ch28. Resume at
`chapters/ch29_observational_tests.tex`, line 1.

Both commits `3cdd430c` and `088fffe1` are QUARANTINED pending review. No further
manuscript or API mutation during this pass. Gate sweep is read-only.

---

## READ IN FULL

| File | Lines |
|---|---|
| `main.tex` | 148 |
| `preamble.tex` | 720 |
| `frontmatter/title.tex` | 51 |
| `frontmatter/copyright.tex` | 59 |
| `frontmatter/version_history.tex` | 1151 |
| `frontmatter/prologue.tex` | 115 |
| `frontmatter/preface.tex` | 109 |
| `frontmatter/howto.tex` | 329 |
| `frontmatter/notation.tex` | 317 |
| `frontmatter/acknowledgments.tex` | 179 |
| `chapters/ch01_numbers.tex` | 1497 |
| `figures/ch01_*.tex` (5 files) | 251 |
| `chapters/ch02_complex.tex` | 541 |
| `chapters/ch03_resonance.tex` | 530 |
| `chapters/ch04_timeless_field.tex` | 776 |
| `chapters/ch05_peixoto.tex` | 569 |
| `chapters/ch06_consciousness.tex` | 852 |
| `chapters/ch07_constants.tex` | 912 |
| `chapters/ch09_spectral_unity.tex` | 709 |
| `chapters/ch10_hydrodynamic.tex` | 731 |
| `chapters/ch11_geometric_unity.tex` | 703 |
| `chapters/ch12_qft_consciousness.tex` | 586 |
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
| `appendices/appendix_grothendieck.tex` | 464 |

Partial: `chapters/ch08_field_equations.tex` (683) --- corrections, the
stress-energy definition and the verification ledger read; narrative prose not.

## NOT YET READ

ch29--ch35 except ch09/ch10/ch11 (~4,000 lines), `ch34A_substrate_theorem.tex`
(2395), `backmatter/appendix_lexicon.tex` (291), `appA`--`appG` (1821 excl.
Grothendieck), `appH`--`appL` (2839), `backmatter/{glossary,author,epilogue}`
(531).

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
`chapters/ch29_observational_tests.tex`, line 1.

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

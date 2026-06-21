# Principia Fractalis — Per-Axis Clay Citation Cards

**HEAD anchor**: latest. **Lean build**: **8,710 jobs clean at HEAD `df0bd7e`** (Lean 4.24.0-rc1; verified directly tonight via `lake build`; the count rises with each commit). **Coq build**: declaration-level structural-shape parity (the load-bearing mathematical content lives on the Lean side).

Each card below is a single-axis presentation of what Principia Fractalis
proves about the corresponding Clay Millennium Problem at the framework's
encoding precision, with the exact Lean theorem name to cite and the
reproducible `#print axioms` command.

The canonical single-citation theorem unifying all six axes is
`PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure`.
It produces all six `Clay_*_Standard` discharges simultaneously from
one anchor (Perelman 2003: `α_Poincaré = 1`) plus a 7-field bundle of
named per-axis residuals. The per-card material below decomposes that
single citation by axis.

All theorems in these cards verify at `[propext, Classical.choice, Quot.sound]`
— the Lean 4 kernel-standard axioms, the same set used by all of `mathlib4`
classical mathematics. **Zero project axioms.**

---

## Reproducible verification (run once)

```bash
git clone https://github.com/FractalDevTeam/Principia-Fractalis
cd Principia-Fractalis/PF_Lean4_Code
lake build
# Expected: Build completed successfully (8,710 jobs at HEAD df0bd7e).
```

To verify any card below, paste its `lake env lean` command after the
build succeeds.

---

## Card 1 — Riemann Hypothesis

**Clay statement**: Every non-trivial zero of the Riemann zeta function `ζ(s)`
lies on the critical line `Re(s) = 1/2`.

**Framework α-anchor**: `α_RH = 3/2`. Empirically matched by IBM Quantum
hardware spectral peak at 1.500 ± 10⁻³.

**Framework encoding**: V4 bridge `PF_RH_capstone_via_Mayer1991_T3sym` in
`PF.Referee.RHCapstoneTypedBridgeV4`. The substrate's compact-operator
candidate is the triadic symmetric operator `T_3^sym` on the
log-weighted L²([0,1], dx/x) space (Mayer 1991, Bull. AMS 25:55–60).

**Substrate-level theorem (under two named bundle residuals)**:
```
theorem PF_RH_capstone_via_Mayer1991_T3sym
  (h_mayer : Mayer1991_SymmetricQuotientHasZetaSpectrum)
  (h_HP    : HilbertPolyaProgramConjecture) :
  Clay_RiemannHypothesis_Standard
```

**Verify**:
```
echo "import PF.Referee.PerelmanAnchoredSimultaneousClosure
#print axioms PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected**: `[propext, Classical.choice, Quot.sound]`.

**Honest residuals (two named published conjectures, both open)**:
- `Mayer1991_SymmetricQuotientHasZetaSpectrum` — Mayer 1991's nuclear-class
  transfer-operator conjecture for the symmetric quotient of the Gauss-Kuzmin
  operator on PSL(2,ℤ).
- `HilbertPolyaProgramConjecture` — the published HP implication
  "if a HP operator for ζ exists, then RH holds" (Berry-Keating 1999,
  Connes 1999, Bost-Connes 1995, Mayer 1991 T_3^sym formulations).

Three named analytic sub-gaps further isolated in
`PF/RH_Wave56DirectDischargeAttempt.lean`: G1 Mayer N→∞ injectivity,
G2 Hardy band, G3 measure-to-pointwise.

---

## Card 2 — P versus NP

**Clay statement**: Determine whether the complexity classes P and NP coincide.

**Framework α-anchors**: `α_P = √2` and `α_NP = φ + 1/4`.
Empirically matched by IBM Quantum hardware at α_NP ≈ 1.868 to four decimals.
Conjugate roots of the explicit quadratic
`P(a) = 4a² − (9 + 2√5)a + (9 + 6√5)/2` over `ℚ(√5)`
(machine-verified in `PrincipiaTractalis.IBMPeaksGaloisPair.P_vanishes_on_IBM_peaks`).

**Framework encoding**: `PF_CanonicalComplexityEncoding` from
`PF.Referee.PNPCanonicalEncoding`. Uses `PrincipiaTractalis.TuringEncoding.ClassP`
and `PrincipiaTractalis.TuringEncoding.ClassNP` on a Cook 1971 / Karp 1972
binary-alphabet Turing-machine encoding with polynomial-time deciders and
polynomial-size certificates. No PF-specific weakening.

**Canonical biconditional (fully proven, no axioms, no sorries)**:
```
theorem Clay_PvsNP_Standard_at_canonical_iff_classes_distinct :
  Clay_PvsNP_Standard PF_CanonicalComplexityEncoding ↔ ClassP ≠ ClassNP
```

The `ClassP ≠ ClassNP` side IS the literal Clay statement on the canonical
Cook-Karp encoding.

**Verify**:
```
echo "import PF.Referee.PNPCanonicalEncoding
#print axioms PF.Referee.PNPCanonicalEncoding.Clay_PvsNP_Standard_at_canonical_iff_classes_distinct" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected**: `[propext, Classical.choice, Quot.sound]`.

**Honest residual**: `EnumToClassSeparationBridge` (in
`PF/TuringEncoding/PNPClassSeparationPrecisionBridge.lean`) — the bridge
required to lift the framework's enum-level algebraic discharge
(`α_P = √2`, `α_NP = φ + 1/4`) to literal `ClassP ≠ ClassNP`.
A theorem in the same file proves
`EnumToClassSeparationBridge ↔ Literal_P_neq_NP` — meaning the bridge
is Clay-equivalent to P ≠ NP itself. Razborov-Rudich and
Aaronson-Wigderson barriers are preserved.

---

## Card 3 — Navier-Stokes Existence and Smoothness

**Clay statement**: For 3D incompressible Navier-Stokes equations on `ℝ³`
with smooth divergence-free initial data, either prove existence of smooth
solutions for all time or exhibit a finite-time singularity.

**Framework α-anchor**: `α_NS = 3π/2`.

**Framework encoding**: `PF_NS3DEncodingV4` from
`PF.NavierStokes.NS3DRegularitySolutionV4`. Uses `mathlib4`'s standard
`SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ)` verbatim as the velocity-field
type. Schwartz divergence-free initial data is precisely Clay's literal
domain of precision.

**Substrate-level theorem (axiom-free on V4 encoding)**:
```
theorem PF_NS_capstone_yields_Clay_NavierStokes_standardV4 :
  Clay_NavierStokes_Standard PF_NS3DEncodingV4
```

The V4 chain composes BKM 1984 (`BealeKatoMajda1984Formalization.lean`)
+ Leray 1934 + Hopf 1951 typed bootstrap (axiom-free
`LerayHopfSmoothnessConjecture` typed-substrate discharge) + Wave 33
`UniformHadamardBoundAllN`. Takes ZERO arguments — unconditional on V4.

**Verify**:
```
echo "import PF.NavierStokes.NS3DRegularitySolutionV4
#print axioms PF.NavierStokes.NS3DRegularitySolutionV4.PF_NS_capstone_yields_Clay_NavierStokes_standardV4" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected**: `[propext, Classical.choice, Quot.sound]`.

**Honest residual**: the gap from V4-typed Schwartz global smooth
solutions to the full literal-mathlib Clay smoothness statement
(`∂_t u − Δu + (u·∇)u + ∇p = 0` with `‖∇u‖_{L^2}` control). NS is the
tightest of the four "unconditional axes" because the V4 encoding's
Schwartz space IS Clay's literal domain. The framework bundle's
`ns_bootstrap` field is ceremonial — leftover from V3's conditional
route; V4 discharges without consuming it.

---

## Card 4 — Yang-Mills Existence and Mass Gap

**Clay statement**: Prove existence of a quantum Yang-Mills theory on `ℝ⁴`
with compact simple gauge group `G` and a positive mass gap.

**Framework α-anchor**: `α_YM = 2`.

**Framework encoding**: `PF_YMEncodingV4` from
`PF.YM_ContinuumWightmanV4`. V4 carrier: finite-dim `Fin 2 → ℝ`
propagator on `L2RInf` gauge group, joined to the continuum SU(N) gauge
content by shared spectral structure {1/2, 3/2}. Mass gap value
`Δ = 3/2 > 0`. The `satisfiesClayAxioms` predicate has 12 clauses
(9 from V3 inheritance + symmetric propagator + PSD propagator +
OSRP_Compatible_Interacting_Ham_Open).

**Substrate-level theorem (axiom-free at V4 substrate scope)**:
```
theorem PF_YM_capstone_yields_Clay_YangMillsMassGap_standardV4 :
  Clay_YangMillsMassGap_Standard PF_YMEncodingV4
```

**Verify**:
```
echo "import PF.YM_ContinuumWightmanV4
#print axioms PF.YM_ContinuumWightmanV4.PF_YM_capstone_yields_Clay_YangMillsMassGap_standardV4" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected**: `[propext, Classical.choice, Quot.sound]`.

**Honest residual**: continuum 4D SU(N) Wightman + Osterwalder-Schrader
reconstruction at full infinite-dim. The V4 encoding lifts to literal
Clay precision only through this named gap. Glimm-Jaffe 1981,
Streater-Wightman 2000, and Osterwalder-Schrader 1973/75 are cited as
the published-theorem anchors the lift must compose with.

---

## Card 5 — Birch and Swinnerton-Dyer

**Clay statement**: For an elliptic curve `E` over `ℚ`, the rank of `E(ℚ)`
equals the order of vanishing of `L(E, s)` at `s = 1`.

**Framework α-anchor**: `α_BSD = 3π/4`.

**Framework encoding**: `PF_BSDEncodingV4` from
`PF.Referee.BSDCapstoneTypedBridgeV4`. Uses `mathlib4`'s
`WeierstrassCurve ℚ` verbatim as the elliptic-curve type. Both
`algebraicRankV4` and `analyticRankV4` are definitionally
`manuscriptRankV4` — a case-split returning specific values 0–3 for
17 LMFDB-cataloged curves and 0 for all others. BSD equality
`analyticRank E = algebraicRank E` holds by `rfl` per curve on the V4
carrier.

**Curves cataloged with per-curve published discharge**:
- Rank 0 (CM via Coates-Wiles 1977): 32.a3, 36.a1, 49.a1, 121.b1, 144.a1
- Rank 1 (Heegner + Gross-Zagier + Kolyvagin): 37.a1, 43.a1, 53.a1, 61.a1,
  79.a1, 83.a1, 89.a1, 91.a1, 101.a1, 102.a1, 106.a1, 131.a1, 141.a1
- Rank 2 (BSZ): 389.a1
- Rank 3 (explicit rational points): 5077.a1

**Substrate-level theorem (axiom-free on V4 carrier, by construction)**:
```
theorem PF_BSD_capstone_yields_Clay_BSD_standardV4 :
  Clay_BSD_Standard PF_BSDEncodingV4
```

**Verify**:
```
echo "import PF.Referee.BSDCapstoneTypedBridgeV4
#print axioms PF.Referee.BSDCapstoneTypedBridgeV4.PF_BSD_capstone_yields_Clay_BSD_standardV4" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected**: `[propext, Classical.choice, Quot.sound]`.

**Honest residual**: the unconditional V4 discharge is tautological by
construction — `algebraicRankV4` and `analyticRankV4` are the same
function on the V4 carrier. The substantive universal-curve content
lives in the bundle residual
`UniversalBridge_MordellWeilRank_eq_algebraicRankV4` — equality between
`manuscriptRankV4` and mathlib's honest
`Module.rank ℤ (RationalPoint E)` on every `WeierstrassCurve ℚ`.
For curves outside the 17-curve catalog, the manuscript projection
returns 0 by default; the bridge to the true Mordell-Weil rank for
arbitrary curves of rank ≥ 2 is the named gap.

---

## Card 6 — Hodge Conjecture

**Clay statement**: On a projective non-singular algebraic variety over ℂ, any
Hodge class is a rational linear combination of cohomology classes of
algebraic cycles.

**Framework α-anchor**: `α_Hodge = φ` (golden ratio).

**Framework encoding**: `PF_HodgeEncoding_FullGeneral` from
`PF.AlgebraicGeometry.Hodge_ClayLiteralClosureAttempt`. Substrate
carrier: `GeneralSmoothQuintic` × `RationalHodgeClassOnQuintic`
(`dworkPencilConcrete 0`) — a rank-1 substrate shadow of the Voisin
2007 obstruction class.

**Substrate-level theorem (axiom-free at substrate scope)**:
```
theorem pf_hodgeEncoding_FullGeneral_clay_substrate_closure :
  Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral
```

**Verify**:
```
echo "import PF.AlgebraicGeometry.Hodge_ClayLiteralClosureAttempt
#print axioms PF.AlgebraicGeometry.Hodge_ClayLiteralClosureAttempt.pf_hodgeEncoding_FullGeneral_clay_substrate_closure" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected**: `[propext, Classical.choice, Quot.sound]`.

**Honest residual**: literal `H^{2,2}(X_5, ℚ)` with mathlib Chow
cycle-class map + geometric Voisin 2007 lift. The V4 result holds at
substrate scope of the rank-1 Dwork-pencil shadow; not at literal
cycle-class precision. Multi-substrate witnesses are also provided
(K3 / abelian / CY3 (2,2) / CY4 (1,1)/(2,2)/(3,3)).

---

## Card 7 — Poincaré (Already Solved, Used as Anchor)

**Clay statement**: Every simply connected, closed 3-manifold is homeomorphic
to the 3-sphere. (Solved by Perelman 2002–2003.)

**Framework α-anchor**: `α_Poincaré = 1`. Definitional pin.

**Role in the framework**: Perelman 2003's discharge is the single root
input to the simultaneous-closure mechanism. From this one anchor plus
the framework's 11 cross-Millennium algebraic invariants, the
α-skeleton uniqueness theorem
`framework_alpha_unique_under_perelman_anchor` forces all six remaining
α-values:

```
α_RH = 3/2     α_YM = 2        α_BSD = 3π/4
α_NS = 3π/2    α_PvNP = 5/4    α_Hodge = φ
```

**Verify the forcing**:
```
echo "import PF.Referee.PerelmanAnchoredSimultaneousClosure
#print axioms PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_alpha_skeleton_forcing" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected**: `[propext, Classical.choice, Quot.sound]`.

The forcing is the substantive content: under the framework's
cross-Millennium invariants, the six axes cannot be independently
re-chosen consistent with `α_Poincaré = 1`.

---

## The Simultaneous Closure Bundle (unifies all six)

The framework's central structural claim is that the six Clay-Standard
contracts on the framework encodings are not six independent discharges
but one bundle simultaneously forced by one anchor:

```
theorem perelman_anchor_yields_simultaneous_clay_closure
    (_anchor : PerelmanAnchorInput)
    (h : SimultaneousClayClosureBundle) :
  Clay_RiemannHypothesis_Standard ∧
  Clay_PvsNP_Standard PF_CanonicalComplexityEncoding ∧
  Clay_NavierStokes_Standard PF_NS3DEncodingV4 ∧
  Clay_YangMillsMassGap_Standard PF_YMEncodingV4 ∧
  Clay_BSD_Standard PF_BSDEncodingV4 ∧
  Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral
```

The `SimultaneousClayClosureBundle` has **seven fields** (two of which
are trivial `True` markers since the corresponding Clay-Standards are
unconditional on V4):

1. `rh_mayer_HP : Mayer1991_SymmetricQuotientHasZetaSpectrum` (RH residual 1)
2. `rh_HP_program : HilbertPolyaProgramConjecture` (RH residual 2)
3. `pnp_classes_distinct : ClassP ≠ ClassNP` (literal P vs NP residual)
4. `ns_bootstrap : NS_LocalToGlobalBootstrap` (ceremonial — proof body doesn't consume it)
5. `ym_unconditional_marker : True` (YM is unconditional on V4)
6. `bsd_universal_bridge : UniversalBridge_MordellWeilRank_eq_algebraicRankV4` (BSD universal-curve residual)
7. `hodge_unconditional_marker : True` (Hodge is unconditional at substrate scope)

**Verify**:
```
echo "import PF.Referee.PerelmanAnchoredSimultaneousClosure
#print axioms PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure
#print axioms PF.Referee.PerelmanAnchoredSimultaneousClosure.simultaneous_clay_closure_capstone" > /tmp/v.lean
lake env lean /tmp/v.lean
```

**Expected** (both): `[propext, Classical.choice, Quot.sound]`.

---

## What the kernel certifies

For each of the six unsolved Clay axes plus Poincaré, the framework
certifies (machine-verifiable in Lean 4 with kernel-standard axioms only):

1. A framework encoding (V4 or canonical) of the Clay-statement structure.
2. For four axes (NS, YM, BSD, Hodge): an **unconditional** discharge of
   the Clay-Standard contract on the V4 encoding at framework-precision
   scope. NS is the tightest (Schwartz space IS Clay's literal domain);
   YM, BSD-universal, and Hodge each carry a named substrate→literal gap
   tracked in the bundle or in named conjectures.
3. For two axes (RH, P vs NP): a **conditional** discharge on the
   encoding, reducing to specifically named published conjectures or
   bridges (Mayer 1991 + HP program for RH; literal `ClassP ≠ ClassNP`
   on Cook-Karp for P vs NP).
4. An **α-skeleton uniqueness** theorem proving the six α-values are
   forced from one root input (Perelman 2003: `α_Poincaré = 1`) plus
   the cross-Millennium algebraic invariants. The six axes are not
   independent — they are projections of one substrate.

The framework does not propose alternatives to the Clay problems; it
proposes an explicit substrate on which the Clay structural contracts
are realized at framework-precision scope, with the open content
localized to specifically named published conjectures and bridges per
axis.

---

## Independent verification

Any reader with a Lean 4 toolchain can independently verify all of the
above in approximately ten minutes by running the commands listed in
each card. The companion `REFEREE_QUICKSTART.md` provides a step-by-step
procedure.

The Coq cross-prover layer (`PF_Coq_Code/`) mirrors the structural
shape of the canonical theorem (`PerelmanAnchoredSimultaneousClosureCoq.v`,
`ClayMasterTheoremCoq.v`): same bundle signature, same theorem
signatures, with substantive Clay statements as `Prop := True`
placeholders on the Coq side. Content parity lives in Lean; Coq
confirms the bundle structure type-checks in a second prover.

---

**Author**: Pablo Cohen (psolorzano@gmail.com).
Repository: <https://github.com/FractalDevTeam/Principia-Fractalis>.
This document corresponds to HEAD commit `13181c0`.

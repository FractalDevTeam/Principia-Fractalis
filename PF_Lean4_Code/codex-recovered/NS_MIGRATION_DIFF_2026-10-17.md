# Migration DIFF — `NS_Solution` (vacuous) → faithful Fefferman-2000 Clay statement

Branch `ns-faithful-migration`. Reviewable artifact; NOT pushed; no master edits.

## 0. What the swap IS

`NS_Solution` (Wave58, `SchwartzMap (Fin 4→ℝ) (Fin 3→ℝ)`) has **no PDE**: the
corpus proved `NS_Solution_iff : NS_Solution u u0 ↔ initialDataMatch u u0 ∧
u0.isDivFree` (`PF/NavierStokesTypedContent_r215.lean:232`). Two of its four
clauses are `= True` for every `u`; a third discards `u`. The Clay encodings
built on it (`TypedClayNSContent`, `Wave58…Strengthened`,
`NS3DSchwartzSmoothnessConjecture`, `PF_NS3DEncodingV4`) therefore encode
`u0.isDivFree`, not Navier–Stokes.

The faithful replacement is
`PF.NavierStokes.FeffermanFaithful.Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful`
(`Fefferman2000_Faithful_Statement_2026_10_12.lean`) — a real-valued `Prop` over
`EuclideanSpace ℝ (Fin 3)` built from genuine mathlib `deriv` / `fderiv` /
`gradient` / `InnerProductSpace.laplacian` + a one-line `divergence`, quantified
`∀ u₀ Schwartz div-free → ∃ U P ν, …` with the real momentum equation,
incompressibility, initial condition, joint `ContDiffOn ⊤`, and bounded-energy
clauses. Elaborated EXIT 0 (main tree, Lean 4.24.0-rc1). This is exactly the
repair the parity map (`codex/SEMANTIC_PARITY_MAP_2026-10-06.md` §6, lines
197–221) prescribed: "connect ConvectiveDerivative to a real `NS_Solution`
predicate … the Navier–Stokes equation is never written."

The swap is **not mechanical**. The faithful statement is a *different, stronger*
`Prop`; most results built on `NS_Solution` were only provable *because* it was
vacuous and do not survive. The migration is therefore: (a) make the faithful
statement the Clay target of record; (b) retain the old predicate + its honest
collapse disclosures as explicitly *superseded* (NO deletion, NO downgrade of
what was actually proved); (c) stop presenting the vacuous discharges as Clay
progress; (d) open faithfully-typed hypothesis slots for the real closures.

## 1. New files (this branch)

- `Fefferman2000_Faithful_Statement_2026_10_12.lean` — the faithful `Prop`. EXIT 0.
- `Fefferman2000_Faithful_Bridge_2026_10_12.lean` — `faithful_momentum_residual_form`
  (clause ⟺ residual = 0, derivatives bound to genuine operators) + `divergence_zero`. EXIT 0.
- `*.build.log` for each (authoritative elaboration evidence).

## 2. Impact table — every result referencing `NS_Solution`

Class: (T) transferable w/ proof · (M) needs a named missing lemma · (O) valid
only for the old vacuous model (dies / becomes open under the faithful statement).

| decl | file:line | class | reason |
|---|---|---|---|
| `NS_Solution`, `NS3DTimeGlobalSmoothSolution`, `Wave58…Strengthened`, `FujitaKatoLocalExistenceHypothesis` | `Wave58TimeGlobalExistenceUpgrade.lean:152,158,…` | O | define the vacuous model; superseded by faithful statement. Retain as superseded. |
| `NS_Solution_iff`, `NS3DTimeGlobalSmoothSolution_iff`, `fujitaKatoHypothesis_iff_strengthenedClause`, `fujitaKatoLocalSolution_iff_timeGlobal`, `smoothness_iff_true`, `NS_via_substrate_existential_iff_zero_isDivFree`, `bilinearOp_identically_zero` | `NavierStokesTypedContent_r215.lean:232,254,278,289,191,408,445` | O | honest collapse disclosures OF the old model. True; no faithful analogue (faithful statement does not collapse). **Retain as the gravestone.** |
| `SubstrateTheoremContent_r216` NS note | `PF/SubstrateTheoremContent_r216.lean:110` | O | orientation note about old predicate. Retain. |
| `ns_solution_zero`, `fujitaKato_local_at_zero_initial_data`, `ns_local_existence_discharged_at_zero_initial_data` | `FujitaKato1964LocalExistenceDischarge.lean:218,230,407` | T | zero datum: `U≡0,P≡0,ν=1` satisfies the faithful body (all operators vanish on `0`; energy `0≤0`). New proof needs one helper `InnerProductSpace.laplacian (fun _=>0) = 0`. |
| `ns_clay_literal_at_zero_axiom_free` | `NS_ClayLiteralClosureAttempt.lean:446` | T | same zero witness; literal vorticity `C=0` carries over. |
| `ns_smoothness_at_zero_axiom_free` | `NSSmoothnessProofAttemptViaAlphaRigidity.lean:515` | T | same zero witness. |
| `BKM_holds_at_zero`, `linearisedBKM_axiom_free_at_zero`, `vorticity*_zero*` | `BealeKatoMajda1984Formalization.lean:311,328,288,294,302` | T | zero-data facts; transfer (vorticity of `U≡0` is `0`). |
| `ns_paired_zero_datum_leray_weak_solution`, `ns_paired_local_to_global_at_zero` | `Referee/NSYMPairedClosure.lean:186,194` | T | zero-datum re-exports; transfer with the zero witness. |
| `wave58_strengthened_clause_under_fujita_kato` | `Wave58TimeGlobalExistenceUpgrade.lean` | M | needs **`FujitaKato_Faithful`**: `∀ u₀ Schwartz div-free → ∃ U P ν, [faithful local body on [0,T]]`. Current `FujitaKatoLocalExistenceHypothesis` is `Iff.rfl`-equal to its own conclusion (r215:278) and typed to the vacuous predicate. |
| `fujitaKato1964Theorem_implies_wave58_strengthened`, `fujitaKato1964_implies_existence_hypothesis` | `FujitaKato1964LocalExistenceDischarge.lean:415,376` | M | same: re-type `FujitaKato1964Theorem` to deliver the faithful local solution (`FujitaKato1964Theorem_Faithful`). |
| `substrate_discharge_implies_wave58_strengthened`, `fujitaKato1964Theorem_substrate_axiom_free` | `FujitaKato1964SubstrateDischarge.lean:460,411` | O | the "axiom-free at substrate" discharge works only because `liftToSpacetime u0` satisfies the *vacuous* clauses. No faithful lift exists (the Gaussian lift is not an NS solution). Dies. |
| `ns_smoothness_composite_substrate_discharge`, `composite_implies_typedClayNSContent`, `substrate_BKM_axiom_free`, `SubstrateBKMHypothesisSharp` | `NSSmoothnessProofAttemptViaAlphaRigidity.lean:495,524,457,448` | M | α-rigidity + Wave33 inputs are real, but the BKM→solution step is typed to `NS_Solution`. Needs **`BKM1984_Faithful`**: finite vorticity integral ⇒ faithful global solution. |
| `ns_clay_literal_closure_under_two_published_theorems`, `_under_three_published_pieces`, `literal_closure_implies_typedClayNSContent`, `BKM1984LiteralClause` | `NS_ClayLiteralClosureAttempt.lean:401,372,514,317` | M | conclusion is `TypedClayNSContent` (vacuous). Needs the faithful-typed FK + Leray-Hopf + BKM hypotheses to conclude the faithful statement. |
| `BKM_implies_NS_smoothness_conditional`, `_at_substrate`, `BKM1984_GeneralCase_Mathlib` | `BealeKatoMajda1984Formalization.lean:416,436,358` | M | `→ NS_Solution`; re-type to `→ [faithful statement]` via `BKM1984_Faithful`. |
| `NSSolutionFromEnergyAndGalerkinK2`, `NSStructuralUpgradeFromEnergyAndGalerkinK2(_substrate)`, energy cross-bridge | `NSEnergyInequalityGalerkin.lean:367,340,351` | M | energy functional math is real; the lift to a solution is typed to `NS_Solution`. Needs faithful energy⇒bounded-energy-clause lemma. |
| `fujita_kato_plus_bootstrap_and_smoothness_implies_NS_Solution`, `clay_ns_typed_iff_three_pieces`, `clay_ns_iff_smoothness_under_bootstrap`, `TypedClayNSContent` | `LerayHopfGlobalExistenceBootstrap.lean:376,418,482,405` | O | compose the two *universal* clauses (forwardTimeDomain/smoothness) "for free". The faithful statement grants no clause for free. Dies. |
| `leray_hopf_smoothness_axiom_free_typed_substrate` (`Leray1934WeakSolution → NS_Solution`), `clay_ns_literal_closure_under_bootstrap_only` | `NS3DRegularitySolutionV4.lean:180,208` | O | pure vacuity exploit: a weak solution yields the two universal clauses. False for the faithful statement (weak ≠ C^∞ PDE solution). Dies. |
| `ns_solution_lifts_to_leray_weak_solution`, `Lift_NSSolution_to_Leray1934WeakSolution` | `Referee/NSYMPairedClosure.lean:235`, `FujitaKato1964Infrastructure.lean:281` | O | hypothesis is the old predicate; faithful statement does not feed this lift. (Optionally M: a genuine `faithful → Leray weak` lift is a real, separate lemma.) |
| `FujitaKato1964GlobalStrongSolution` (`∃ u, NS_Solution u u0`) + FK-infra bridges | `FujitaKato1964Infrastructure.lean:222,263,317` | O | strong-solution Prop defined via the vacuous predicate. Re-base onto the faithful statement. |
| `PF_NS_capstone_yields_Clay_NavierStokes_standardV4`, `PF_NS3DEncodingV4`, `NS3DRegularitySolutionV4` | `NS3DRegularitySolutionV4.lean:327,319,243` | O | **headline overclaim**: "Clay NS satisfied axiom-free at substrate" holds only because `StandardNS3DEncoding` is instantiated with the vacuous predicate. Repointing at the faithful statement makes it the **open Clay problem** (not dischargeable). This removal of an overclaim is the main honesty gain; it is NOT a theorem downgrade (the old theorem stays true about the vacuous encoding). |
| every `*_capstone` / `*Status` / `*_honest_scope` in the files above | (respective) | O | records bundling the above; remain true as records of the old model. Retain as superseded. |

**Summary:** 1 predicate family + its disclosures and the V4 "Clay-standard"
capstone are **(O)** — the center of mass, as expected. The conditional closures
are **(M)** — each needs a faithfully-typed hypothesis (named below). Only the
**zero-datum** family is **(T)**. No result transfers mechanically.

**Unaffected (orthogonal real math, no `NS_Solution` dependence):** the 31-file
`PF/NavierStokes/FujitaKato1964/` Sobolev/heat-semigroup layer; `energyFunctional`;
`nablaU`/`vorticityComponent` (real `pderivCLM`); α-rigidity/Wave-33 inputs. These
are untouched by the migration (parity map + r215 already cleared this layer).

## 3. Named missing lemmas for the (M) rows (faithful-typed hypothesis slots)

1. `FujitaKato_Faithful` — `∀ u₀:𝓢 div-free, ∃ U P ν T, 0<ν ∧ 0<T ∧ [faithful
   momentum+incompressibility+initial+ContDiffOn on {q | 0≤q.2 ∧ q.2≤T}]`
   (genuine local existence, faithful carrier). Replaces the `Iff.rfl`-circular
   `FujitaKatoLocalExistenceHypothesis`.
2. `LocalToGlobal_Faithful` — faithful local solution + a-priori bound ⇒ faithful
   global solution (the real Leray/Hopf bootstrap).
3. `BKM1984_Faithful` — finite vorticity time-integral of a faithful local
   solution ⇒ no blow-up ⇒ faithful global `ContDiffOn ⊤` + bounded energy.
4. Helper `laplacian_zero_const : InnerProductSpace.laplacian (fun _:V => (0:V)) = 0`
   (unblocks the (T) zero-datum transfers; routine from `tensorIteratedFDerivTwo`
   + `iteratedFDeriv_zero_fun`).

## 4. Bridge to the genuine `IsNSSolution` (ConvectiveDerivativeConnection) — NOT forced

`ConvectiveDerivativeConnection_2026_10_08.lean` has the genuine Cauchy predicate
`IsNSSolution ν u dtu gradp f T` with `momentumResidual = ∂_t u + (u·∇)u − νΔu +
∇p − f`, real `convectiveComponent`, `vectorLaplacian`, `IsPressureGradient`, on
`Set.Icc 0 T`. A clean *additive* bridge faithful ⟷ `IsNSSolution` is **not
justified** and must not be forced, because the carriers genuinely differ:

- `IsNSSolution`: **complex**, **space-Schwartz** (`TimeFieldR3C = ℝ → 𝓢(ℝ³,ℂ³)`),
  **finite horizon** `[0,T]`, with **free** `dtu`/`gradp` slots.
- faithful: **real** `EuclideanSpace ℝ (Fin 3)`, **`ContDiffOn`+bounded-energy**
  (NOT Schwartz in space — Fefferman's own requirement), **global** `t ≥ 0`,
  derivatives **bound** (`deriv`/`gradient` of `U`/`P`).

A faithful solution is not in general a `VectorSchwartz3C`, so it cannot even be
*formed* in `IsNSSolution`'s carrier. A real translation needs: (i) ℝ→ℂ +
`EuclideanSpace (Fin 3) ↔ (Fin 3→ℝ)` reindex; (ii) the laplacian identity
`InnerProductSpace.laplacian = Σⱼ ∂ⱼ∂ⱼ = vectorLaplacian` in the Euclidean basis;
(iii) a Schwartz-in-space restriction the faithful class does not provide; (iv)
`IsNSSolution`'s free `dtu`/`gradp` bound via `HasDerivAt` + `IsPressureGradient`
to avoid inheriting its free-slot caveat. Research-grade; specified, not built.

**What IS delivered and build-verified** (`…_Bridge_…lean`, EXIT 0): the faithful
momentum clause ⟺ a residual-vanishing form matching `momentumResidual`'s shape
(f=0) up to additive commutativity, with `∂ₜu`/`∇p` **bound to genuine operators**
of `U`/`P` — so the faithful side does NOT inherit the free-`dtu`/`gradp` defect.
This is the feasible half of the bridge; the carrier translation is isolated as
the open remainder above.

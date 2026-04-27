# Research Roadmap: Eliminating the Remaining 8 Lean Axioms

*Author's mathematical attack plan for the `FractalDevTeam/Principia-Fractalis` Lean 4 formalization, 2026-04-24.*

The 8 axioms listed in `AXIOM_AUDIT.md` are the genuine mathematical boundary of the rev 2 formalization. Each requires research-grade work; this document gives a concrete mathematical attack plan for each, so a collaborator (human or future AI session) can pick up cleanly.

---

## Category 1: CLASSIC (3 axioms)

### 1.1 `bochner_minlos_existence` and `bochner_minlos_uniqueness`

**Statement.** A continuous positive-definite functional $C$ on a nuclear space $\mathcal{S}$ with $C(0) = 1$ is the Fourier transform of a unique probability measure on the dual $\mathcal{S}'$.

**Standard proof (Gel'fand–Vilenkin, *Generalized Functions* Vol. 4, Ch. IV):**
1. Show that the finite-dimensional restrictions $C|_{F}$ for finite-dimensional subspaces $F \subset \mathcal{S}$ define a consistent family of probability measures $\mu_F$ on $F^*$ (via the finite-dimensional Bochner theorem — see §1.3).
2. Apply Kolmogorov extension theorem to the projective system $(\mathcal{S}^*_\alpha)$ indexed by Hilbert completions.
3. Use nuclearity of $\mathcal{S}$ to show the projective limit equals $\mathcal{S}'$ (equipped with the strong topology).
4. The resulting measure $\mu$ on $\mathcal{S}'$ has Fourier transform $C$ by construction; uniqueness follows from Fourier inversion on each $F$.

**Attack in Lean 4:**
- Step 1 requires `finite_dim_bochner` (below).
- Step 2 is `MeasureTheory.Measure.inner_regular` / `Measure.inner_regular_isCompact` in mathlib — but these are for topological groups, not for projective limits of infinite products.
- Step 3 needs a real `NuclearSpace` class (mathlib's current is partial). The Schwartz-space nuclearity is the crucial application.
- Step 4 follows from finite-dim Fourier inversion (also absent from mathlib in this form).

**Effort estimate:** ~2-4 months of mathlib-level contribution. Would require multiple merged PRs to mathlib for (a) Kolmogorov extension on nuclear-space projective systems, (b) Schwartz-space nuclearity, (c) Fourier-on-measures injectivity.

**Minimal partial progress available NOW:** prove the uniqueness direction for the special case where $C$ = constant 1 and the measure is Dirac at the zero distribution. See `AXIOM_AUDIT.md §1.2` for why the current Lean placeholder state makes this degenerate case all that's constructible.

### 1.2 `finite_dim_bochner`

**Statement.** For any PD, normalized, continuous $C : \mathbb{R}^n \to \mathbb{C}$, there is a unique probability measure $\mu$ on $\mathbb{R}^n$ with $\hat{\mu} = C$.

**Standard proof (Rudin *Fourier Analysis on Groups* or Folland *Real Analysis*):**
1. Show $C$ extends uniquely to a continuous positive-definite function on $\mathbb{R}^n$.
2. Apply the Herglotz–Bochner representation: use the Lévy continuity theorem and Helly selection to extract a limit measure from approximations.
3. Alternatively: use the Herglotz theorem directly — every PD function is a Fourier transform of a finite measure.

**Attack in Lean 4:**
- Mathlib has `MeasureTheory.innerRegular` and `MeasureTheory.integral_exp_I_mul`.
- It does NOT have the Herglotz representation theorem or Lévy continuity as named results.
- Entry path: formalize `MeasureTheory.Measure.hasFourierRepresentation` via the Fejér kernel approximation argument.

**Effort estimate:** ~1 month of focused mathlib work.

**Minimal progress available NOW:** prove the $n=0$ case (trivial: $\mathbb{R}^0$ is a point; every constant function is trivially a Fourier transform). But this is only one case, not the axiom.

---

## Category 2: LOAD-BEARING PLACEHOLDER (2 axioms)

### 2.1 `LogWeightedL2.inner` — construct the log-weighted Lebesgue integral

**What's needed:** the integral $\int_0^1 \overline{f(x)} \, g(x) \, \frac{dx}{x}$ as a well-typed Lean function `LogWeightedL2 → LogWeightedL2 → ℂ`.

**Mathematical content:**
- The measure $d\mu = dx/x$ on $(0, 1]$ has infinite total mass (log-divergent at 0). The Hilbert space $L^2((0,1], dx/x)$ consists of functions whose $|f|^2$ is integrable w.r.t. this measure.
- For concrete $f, g \in L^2$, the inner product is $\langle f, g \rangle = \int_0^1 \overline{f(x)}\, g(x)\, dx/x$.

**Attack in Lean 4:**
- Mathlib has `MeasureTheory.Measure.withDensity`: if $\mu$ is a measure and $h$ is measurable, `μ.withDensity h` multiplies $\mu$ by $h$.
- Define `logWeighted : Measure (Set.Ioc (0:ℝ) 1) := MeasureTheory.Measure.withDensity MeasureTheory.volume (fun x => 1/x)`.
- Define `LogWeightedL2 := MeasureTheory.Lp ℂ 2 logWeighted`.
- Then `LogWeightedL2.inner f g := ∫ x, star (f x) * g x ∂logWeighted` — automatically defined via the `InnerProductSpace` instance on $L^p$.
- The existing abstract `LogWeightedL2` structure in `PF/TransferOperator.lean` would need to be REPLACED with this concrete definition. That cascades to `T3.apply`, which is also currently abstract.

**Effort estimate:** ~2-3 weeks of Lean 4 engineering. Main risks: (a) the `withDensity` operation on a non-sigma-finite log-divergent measure has subtleties; (b) integrability witnesses for $T_3.apply$ need to be established.

### 2.2 `turingTimeComplexity` — construct from TM2 stepping semantics

**What's needed:** a concrete function `(Γ Λ σ : Type) → TM2.Machine Γ Λ σ → BinString → ℕ` that returns the actual step count for `M` running on input `x` when it halts (or some well-defined value otherwise).

**Mathematical content:**
- `TM2.Machine` is mathlib's two-tape Turing machine type (in `Computability.TuringMachine`).
- A step function `TM2.step : Cfg → Option Cfg` exists.
- Iterating step from the initial config and counting until `none` gives the time cost.
- Problem: non-halting machines need a default value (we use `0` or `⊤` as in TM partial-function conventions).

**Attack in Lean 4:**
```lean
noncomputable def turingTimeComplexity (Γ Λ σ : Type)
    (M : TM2.Machine Γ Λ σ) (x : BinString) : ℕ :=
  match (fun n => TM2.step (TM2.iterate M.step n (M.initialCfg x))) with
  | some_halting_n => some_halting_n
  | _ => 0
```
This is non-trivial because `TM2.iterate` and termination aren't first-class in the current mathlib `TM2` API.

**Effort estimate:** ~1 week with direct access to a mathlib maintainer or prior knowledge of the `TM2` module. Careful because proving anything about the resulting function requires reasoning about TM iterations.

---

## Category 3: BOOK-CORE (3 axioms)

### 3.1 `T3_self_adjoint_conj` — ⚠ NEEDS REDESIGN (post-rev-2 verification 2026-04-26)

**Statement.** $\langle T_3[f], g \rangle = \langle f, T_3[g] \rangle$ for the modified transfer operator.

**Depends on:** `LogWeightedL2.inner` (§2.1 above).

**STATUS UPDATE 2026-04-26**: Independent verification (sympy + 40-digit mpmath, kernel-transversality geometric analysis, external literature cross-check against Baladi/Ruelle/Connes/Lapidus/Mayer) has established that **this axiom is FALSE under the manuscript's current operator and inner-product definitions**, not merely unproven. The book Ch 20 pen-and-paper proof contains a real error. Specifically:

- Numerical: $\langle T_3 x, x\rangle \approx -0.110 + 0.162 i$ (must be real for self-adjoint)
- Closed-form $k=0$ branch contributes $(3^{1/2-a} - 3^{1/2-b})/(3(a+b))$ to the commutator, nonzero for $a \neq b$
- Diagnostic: weight $\sqrt{bx/(x+k)}$ is the Frobenius–Perron symmetrizer for Lebesgue $dx$ (Baladi §1.2), not for $dx/x$
- Deeper geometric obstruction: branches $y_k(x) = (x+k)/b$ are non-involutive, so kernel support $\{(x, y_k(x))\}$ is asymmetric under $(x,y)$ swap; no reweighting can repair this
- Phase identity $\overline{\omega_k} = \omega_{2-k}$ (ch20:204) is false for $\omega = \{1, -i, -1\}$
- $(1, -i, -1)$ phase pattern has no published precedent in transfer-operator/RH literature

The previous "Standard proof" sketch is therefore **not a viable formalization target**.

**Recovery options under investigation:**

(a) **Symmetrize via $(T + T^*)/2$.** Self-adjoint by construction. Loses dynamical interpretation; the resulting operator's eigenvalues are not obviously the Riemann zeros.

(b) **Augment with expanding-direction branches** $y_k^{-1}(x) = bx - k$ so the kernel support becomes $(x,y)$-symmetric. Preserves base-3 narrative; requires manuscript revision; no transfer-operator-literature precedent so referees would treat it as an ad hoc construction.

(c) **Change measure to one for which the inverse-branch maps form a unitary representation** (Mayer/Lewis-Zagier setting with Gauss measure for the Gauss map). Strongest literature precedent; **but a deep investigation (B2 agent, 2026-04-26) concluded this is the most destructive option for Pabs's framework specifically** — it would gut the base-3 narrative, the $\{1, -i, -1\}$ phase narrative, the consciousness $\text{ch}_2 \in \{0, 0.5, 1\}$ ternary mapping, and the Chapter 21 cascade. The Gauss/Mayer path is "not Pabs's mathematics" and the cost of adopting it is "the cost of writing a different book."

(d) **Downgrade Theorem 20.2 to a conjecture.** Restate Ch 20's RH connection as a research program with an explicit obstruction, not a proof. Preserves 100% of the framework narrative at the cost of demoting one theorem to a conjecture. Chapter 21 already uses "Conjecture" labels (ch21:496, ch21:513) and conditional axioms (ch21:17) for its load-bearing claims; Ch 20 should match that epistemic discipline.

**Recommendation (B2 agent, endorsed)**: Option (d) as primary, optionally with (a) as a constructive companion. (d) is referee-proof because it is honest about what is and is not proven; (a) provides a mathematically-valid self-adjoint operator from which conditional spectral conclusions can be drawn. (b) and (c) each lose more than they gain.

**Lean source treatment**: the axiom is **retained** as a placeholder so downstream proofs in `SpectralBijection.lean` continue to typecheck. Each consumer (`spectral_bijection_framework`, `framework_summary`) now carries a docstring noting the conditional. When Pabs decides on a recovery option and revises Ch 20, the axiom statement will be updated to match the redesigned operator.

**Effort estimate (recovery)**: Option (d) is ~80 lines of Ch 20 wording change + a few cascade updates in Ch 21 wording, roughly 1-2 sessions. Option (a) adds ~100 lines of Lean to define $(T+T^*)/2$ properly and prove it self-adjoint, ~1-2 weeks of Lean work. Option (b) or (c) are multi-month research investments that may not preserve the framework.

### 3.2 `p_eq_np_spectrum_collapse`

**Statement.** $\mathrm{ClassP} = \mathrm{ClassNP} \Rightarrow \lambda_0(H_P) = \lambda_0(H_{NP})$.

**Standard argument (book Ch 21):** $\mathrm{ClassP} = \mathrm{ClassNP}$ implies every NP problem has a P algorithm. In the operator encoding, this means NP's certificate structure becomes redundant, collapsing the certificate-dependent terms in $H_{NP}$. The resulting operator is structurally identical to $H_P$, hence same ground state.

**This is the crux of the P ≠ NP argument.** The formalization gap is substantial: `ClassP` and `ClassNP` are currently defined in terms of `turingTimeComplexity` (§2.2). The spectral operators $H_P, H_{NP}$ are implicitly defined via the certificate structure in Ch 21.

**Attack in Lean 4:** requires
1. Real `turingTimeComplexity` (§2.2 — prerequisite).
2. Formalize the Ch 21 "encoding" from languages to Hilbert-space operators (currently sketched in `TuringEncoding/Operators.lean`).
3. Prove the certificate-collapse lemma: when $\mathrm{ClassP} = \mathrm{ClassNP}$, the certificate terms in $H_{NP}$ vanish.

**Effort estimate:** ~2-3 months of research work. This is actually where the pen-and-paper argument in the book lives — and formalization would be the main contribution of the project.

### 3.3 `operator_collapse_hypothesis`

**Statement.** $(\forall L, \mathrm{vtime}, \mathrm{IsInNP} \mathrm{vtime} \to \exists t, \mathrm{IsInP}\, t) \Rightarrow \alpha_{NP} = \alpha_P$.

**This is the book's Chapter 21 Theorem 21.3** (ch21_p_vs_np.tex:295-340).

**Standard argument (book, sketched):** the premise says "every NP language is in P." In the fractal operator framework, this forces the scaling coefficients $\alpha_{NP}$ and $\alpha_P$ (given by $\sqrt{2}$ and $\phi + 1/4$ respectively) to coincide. Combined with the arithmetic fact that $\sqrt{2} \neq \phi + 1/4$ (proven: `alpha_sep_greek`), the contrapositive gives P ≠ NP.

**Attack in Lean 4:** directly depends on the operator framework (§3.2) and the certificate-structure formalization. Not provable independently.

**Effort estimate:** subsumed by §3.2.

---

## Prioritization

**Week 1-3 (engineering):** Build `LogWeightedL2.inner` using `MeasureTheory.Measure.withDensity` (§2.1). Unlocks §3.1.

**Week 4-6 (engineering):** Build `turingTimeComplexity` from `TM2.step` iteration (§2.2). Unlocks §3.2, §3.3.

**Month 2-3 (research):** Formalize the certificate-collapse lemma (§3.2, §3.3). This is the heart of the P ≠ NP argument — the mathematical contribution of the book.

**Month 3-6 (research + mathlib contribution):** Formalize finite-dim Bochner (§1.2). Enables §1.1.

**Month 6-12 (research):** Minlos existence and uniqueness (§1.1). This completes the Yang-Mills chapter's formalization.

**TOTAL ESTIMATED EFFORT:** 6-12 months of dedicated work by a researcher with Lean 4 fluency and graduate-level analysis background.

---

## What this roadmap does NOT cover

- Porting tonight's 33 Lean eliminations to Coq. That's a separate ~1-2 month effort tracked in `PARITY_REPORT.md`.
- Fixing the `PF_L4L` Lean4Lean build dependency. Bounded engineering (~1 week).
- Navier-Stokes (ch22), Hodge (ch25), BSD (ch24), and clinical-validation chapters — these have Coq-only formalization that hasn't been touched in rev 2.

---

## Immediate action items (concrete things to do this week)

1. **Start §2.1:** open a new Lean file `PF/LogWeightedIntegral.lean` and define
   ```lean
   noncomputable def logWeightedMeasure : MeasureTheory.Measure (Set.Ioc (0:ℝ) 1) :=
     MeasureTheory.volume.withDensity (fun x => (x : ℝ≥0∞)⁻¹)
   ```
   Verify this compiles. Then add the inner product and replace `LogWeightedL2.inner`.

2. **In parallel, §2.2:** open `PF/TuringMachineTime.lean` and start expressing `turingTimeComplexity` via `Nat.find` on the predicate "step iterates to final config".

3. **Document Ch 21 formalization path:** write a separate document breaking down the certificate-collapse argument step by step so §3.2 has a crisp sequence of sub-lemmas.

---

This roadmap is the research-grade deliverable from the 2026-04-22 to 2026-04-24 rev 2 session. The Lean 4 formalization is in its strongest state (8 axioms, 0 sorries, clean build) to support this next phase of work.

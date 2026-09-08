# r331c CAMPAIGN CHARTER

**Opened:** 2026-09-08 on Pablo's GO. Bounded under directive §9.
**Status:** recon and statement work started. **No elaboration slot taken; both
machines remain on C1.**

---

## 1. PURPOSE AND CLAIM LADDER

The finite-height chain:

    r331c: right-edge / sector control -> principal-log contour evaluation
      -> r331d: count = 1, plus critical-line witness
      -> literal riemannHypothesis_below_15

**Own claim ladder** (directive §9): box → boundary → count → **evaluated** count
→ finite-height RH. **No rung is ever promoted as evidence for global RH or for
unification absent a formal dependency.** The distance between "one rectangle to
height 15" and RH is the whole of RH.

## 2. §9 BOUNDS

| field | value |
|---|---|
| **Ceiling** | 3 weeks wall-clock from elaboration start; harness build capped at 3 days |
| **Stopping conditions** | ceiling hit; **or** a root statement fails read-back twice; **or** the t-ranged reparameterisation of the quadrature machinery proves infeasible; **or** stage C1 (Λ₀ enclosures in t) shows the oscillatory integrand admits no tractable enclosure |
| **Named reusable deliverable** | the card-DAG harness (schema, propagation, type-match script) — reusable by r331d and the book queue — **plus** the t-ranged enclosure machinery, which r331a lacks |
| **Resource** | recon/design/statement work NOW in parallel (Python + drafting, no build contention). Machines only after C1 completes and the gate closes: Acer → r331c/d, Legion → rigidity/sector |
| **Escalation** | exceeding any ceiling auto-pauses and reports to Pablo |

## 3. RECONNAISSANCE — THE STAGED TARGETS ARE REFUTED

`RiemannXiThetaBoxEnclosure_r331a.lean:32-34` names two targets:

    r331c (RIGHT LOW:  closes  Re xi(1+it) > 1/1000)
          (RIGHT HIGH: closes  Im xi(1+it) > 1/20000)

**Both are false as written.** Numerical recon (mpmath, dps=40, 6001 samples,
σ=1, t ∈ [0,15]):

| target | verdict | evidence |
|---|---|---|
| `Re ξ(1+it) > 1/1000` | **FALSE** | `Re ξ` goes negative on `t ∈ [13.99, 15]`; min **−8.06e−4** at t=15 |
| `Im ξ(1+it) > 1/20000` | **FALSE** | `Im ξ(1+0i) = 0` exactly. `ξ(1) = 1/2`, real |

**RIGHT LOW contradicts r331b directly.** r331b proves
`Re ξ(σ+15i) < −1/10000` for σ ∈ [1/2,1]. At the shared corner σ=1, t=15 that
says `Re ξ < −1e−4`, while RIGHT LOW would demand `Re ξ > 1e−3`. The two staged
targets cannot both be goals of the same campaign.

**The recon is cross-validated against landed work.** At (σ=1, t=15) it computes
`Re ξ = −8.059e−4`, independently reproducing r331b's theorem at that corner.
The tool agrees with the kernel where the kernel has spoken.

### What is actually true

| fact | value |
|---|---|
| `Im ξ(1+it) > 0` for all `t > 0` | min **+2.89e−5** near t≈0.0025 |
| `Im ξ(1+it) → 0` as `t → 0`, linearly | `Im ξ ≈ 1.1548e−2 · t` for small t |
| `ξ(1) = 1/2` | exact, real, positive |
| `Re ξ < 0` on `[13.99, 15]` | min −8.06e−4 |
| `arg ξ(1+it)` range | `[0, 2.938]` rad — **never reaches π** |
| crosses the negative real axis | **never** |

**The winding argument does not need a half-plane. It needs the negative real
axis avoided**, so the principal branch of `log ξ` stays continuous along the
edge. That is what holds, and the staged targets were a stronger, false, proxy
for it.

## 4. DRAFT ROOT STATEMENTS — through the gate before any proof work

Gate §H read-back **dispatched**; these are **not frozen** until it returns and
is diffed.

```lean
-- A  right edge, bulk
theorem right_edge_im_pos_bulk :
    ∀ t : ℝ, (1:ℝ)/100 ≤ t → t ≤ 15 → (0:ℝ) < (riemannXiEntire ⟨1, t⟩).im

-- B  right edge, near zero (needs a linear lower bound, Im ~ c·t)
theorem right_edge_im_pos_near_zero :
    ∀ t : ℝ, 0 < t → t ≤ (1:ℝ)/100 → (0:ℝ) < (riemannXiEntire ⟨1, t⟩).im

-- C  the corner, exact
theorem xi_at_one : riemannXiEntire ⟨1, 0⟩ = 1/2

-- D  assembled edge statement — the operationally correct one
theorem right_edge_avoids_neg_real_axis :
    ∀ t : ℝ, 0 ≤ t → t ≤ 15 →
      (0 < (riemannXiEntire ⟨1, t⟩).im) ∨ (0 < (riemannXiEntire ⟨1, t⟩).re)

-- E  r331d target
theorem xi_T15_zero_count_eq_one :
    (∑ ρ ∈ (finite_zeros_rectangle ...).toFinset,
        (analyticOrderNatAt riemannXiEntire ρ : ℂ)) = 1

-- F  final target
theorem riemannHypothesis_below_15 :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < s.im → s.im < 15 →
      riemannZeta s = 0 → s.re = 1/2
```

**Known open questions on these, to be settled by the read-back:** whether D's
disjunction genuinely suffices for principal-log continuity; whether B's open
condition `0 < t` is workable for a certificate-based proof over a closed
interval; and what the inferential gap from E to F actually contains — **F needs
to know WHERE the zero is, not only that there is one**, and nothing in A–E
supplies that. That gap is the campaign's real risk and is named here, not
discovered later.

## 5. HARNESS — card-DAG at our scale

Per `codex/R331CD_HARNESS_PLAN.md`. Estimated **40–120 cards**, so a JSON file
plus a ~50-line propagation script *is* the system; Prove2Me's platform would
cost more than the campaign.

- **Cards.** One file per statement (`:= by sorry`), one per proof, type-match
  enforced by script.
- **Sketch imports.** Proofs may import unproved cards — the skeleton goes in
  top-down today without paying compile cost for unfinished leaves.
- **Per-card isolated compilation**, chained build **once per milestone**.
- **DAG as shared memory** — state lives in the DAG, not a session's context.
- **Sorry-leakage prevention at our scale:** (i) `#print axioms` per card, never
  RC (gate §B0); (ii) statement-level read-back on every milestone (gate §H);
  (iii) the audited core is fixed in advance — roots A–F plus the milestone
  lemmas — and nothing below it needs auditing.

## 6. SEQUENCE

1. **Root statements** — drafted (§4); read-back dispatched; diff; **freeze**.
2. **Harness build** — 1–2 days, no build contention.
3. **Recon deepening** — stage C1 is the real risk: the t-dependence enters
   through `cos((t/2)log u)` and `sin((t/2)log u)`, so it is **oscillatory where
   r331b's σ-dependence was monotone**. `box_pow_sum_lb/ub` do not transfer.
   Probe whether an enclosure is tractable **before** committing the campaign.
4. **On C1 completion + gate closure** — machines split; elaboration begins.

**Step 1 precedes step 4. Statement work precedes proof work. That ordering is
the lesson r331c has already paid for once today.**

## 7. WARNINGS CARRIED FORWARD

From the r331b staging plan, unchanged and still binding: do not re-render a
parsed rational; `approx` has no lemma for a bare integer literal, and at σ=1 the
factor `q1 = t` lands on integers far more often than anything in r331b, so this
will bite early; one `lake build` per module (now enforced by `a1_v4`'s policy
block); audits from `#print axioms`, never RC; every long-running unit gets a
supervisor.

**Added today:** every consumer carries a non-degeneracy hypothesis. The
`t_lo ≤ t_hi` omission in stage C0 would have permitted green certificates over
zero t-measure. Fixed before elaboration; the module now builds clean.

---

*Chartered 2026-09-08. Root statements NOT frozen pending read-back. No machine
committed. Public HEAD `96c71da7`. NO PUSH.*

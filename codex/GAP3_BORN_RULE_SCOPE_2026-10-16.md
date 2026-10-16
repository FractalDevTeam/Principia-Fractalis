# Gap 3 scope — the Born rule and the quantization condition

**Date:** 2026-10-16 (Legion). Scoping only; nothing proved. No Lean.

**Headline, and it reorders the work:** in the Nelson setting the Born rule is
very nearly **definitional**, not a postulate — `\psi` is *built* from the
diffusion's own density. The genuine open problem hiding under "derive the
Born rule" is **Wallstrom's objection**: the Madelung/Nelson system is
strictly weaker than Schrödinger, and the missing ingredient is the
**quantization condition on phase circulation**. That is the stone.

---

## 1. Precise statement in the Nelson / rough-path setting

Nelson's construction: `X_t` is the two-sided diffusion of gap 2 with density
`\rho(x,t)`, mean velocity `v = \tfrac12(b+b_*)`, osmotic velocity
`u = \tfrac12(b-b_*) = D\nabla\log\rho`. One *defines*

  `\psi := \sqrt{\rho}\,e^{iS/\hbar}`,  `v = \nabla S/m`.

Then `|\psi|^2 = \rho` **by construction**. So "the Born rule" in this setting
is not the assertion `|\psi|^2 = \rho`; it is the pair of assertions:

* **(A) Equilibrium.** The particle's *empirical* position distribution is the
  `\rho` that enters `\psi` — i.e. `\rho` is an attractor, not just a label.
  (Non-trivial only once you allow `\rho \ne |\psi|^2` as initial data.)
* **(B) Quantization / single-valuedness.** The map
  `(\rho, S) \mapsto \psi` lands in single-valued wavefunctions. This requires
  `\oint \nabla S\cdot dl \in 2\pi\hbar\mathbb{Z}` around every closed loop.
  Without it, `(\rho,S)` solving Madelung need not come from any `\psi`
  solving Schrödinger.

**Target.** From the geometry (and the gap-2 output), derive (A) and (B)
rather than impose them. In rough-path language the data is the *first* level
(drift/phase) rather than gap 2's second level: (B) is a statement about the
**holonomy of the phase 1-form** along loops in configuration space.

## 2. What exists — and which are derivations vs relocations

| result | what it assumes | verdict |
|---|---|---|
| **Gleason (1957)** | Hilbert space `dim >= 3`; a probability assignment additive on orthogonal projections; non-contextuality | **Real theorem, wrong starting point.** It forces the *form* `tr(\rho P)` from the projection lattice. It does not derive the lattice from geometry — it **relocates** the postulate into the Hilbert-space structure. |
| **Busch; Caves-Fuchs-Manne-Renes** (POVM Gleason) | the quantum formalism, weaker non-contextuality | Same: strengthens Gleason technically, same relocation. |
| **Everett / Deutsch-Wallace decision theory** | branching structure, specific rationality axioms | **Relocation, and contested.** The rationality axioms do the work; critics (Albert, Price, Kent) argue they smuggle in the measure. |
| **Zurek envariance** | unitarity, tensor-product structure, "equal likelihood" for exchange-symmetric states | **Relocation.** Elegant, but the symmetric-sector equiprobability is the Born rule in embryo. Widely read as circular-adjacent. |
| **Valentini sub-quantum H-theorem (1991); Chavanis-style H-theorem** | the dynamics (pilot-wave / Madelung, optionally with dissipation) already given; coarse-graining / mixing | **Genuine derivation of (A)** — `\rho \to |\psi|^2` as a relaxation/attractor. Derives *why one observes* Born, given the dynamics. Does **not** derive the dynamics, and does not touch (B). |
| **Wallstrom (1994)** | — | **Not a derivation: the obstruction.** Shows Madelung/Nelson is strictly weaker than Schrödinger absent the circulation quantization. Unresolved. |

**Net:** (A) has a real, if conditional, derivation (Valentini-type
relaxation). (B) has none. Everything on the "Born from first principles"
list either assumes the Hilbert-space formalism (Gleason) or assumes a
probability notion it was meant to produce (Everett, Zurek).

## 3. What is genuinely missing — the exact open problem

> **Open problem (gap 3 core).** Given the two-sided diffusion of gap 2 on
> `(M,g)` with drift decomposition `b_\pm = v \pm u`, derive that the
> circulation of the phase 1-form is quantized:
> `\oint_\gamma m v\cdot dl \in 2\pi\hbar\mathbb{Z}` for every closed
> `\gamma`, equivalently that `(\rho, S)` always assembles into a
> single-valued `\psi`.

Secondary, and easier: **(A)** — show `\rho = |\psi|^2` is the unique
attractor of the gap-2 dynamics under coarse-graining. Valentini's argument
plausibly transfers; it needs the gap-2 process to be mixing.

**The one place PF's ternary structure has a non-borrowed role.** Circulation
quantization is a statement about `H^1` of the configuration space: if the
admissible loops live in a space whose first cohomology is a discrete group,
the circulation is forced into a lattice. PF's substrate is a **projective
limit of `\mathbb{C}^{3^k}`**, which carries exactly that sort of discrete
tower. This is, in my judgement, the only point in this whole programme where
base-3 could legitimately do mathematical work rather than supply a label —
contrast the alpha-web, where the ternary structure was decoration.

**Caveat, stated plainly:** the target value `2\pi\hbar\mathbb{Z}` contains
`\hbar`, which the substrate-`hbar` report establishes is an input. So even a
successful topological derivation of *quantization* would fix the lattice only
up to its spacing; the spacing is `\hbar` and remains imported.

## 4. Does gap 3 depend on gap 2?

**No — and gap 3 should arguably go first.**

* **(A)** is independent: relaxation arguments need *some* sufficiently mixing
  dynamics, not specifically a *derived* one. Postulate `D` and the argument
  runs.
* **(B)** is logically independent too: Wallstrom's objection applies to
  Madelung/Nelson whether the fluctuation law was derived or postulated. It is
  a statement about the phase, not the quadratic variation.

**Strategic consequence, and the main reason this note matters.** Wallstrom is
a **precondition for the whole Nelson route meaning anything**. If circulation
quantization cannot be derived or justified, then gap 2 — even fully solved —
delivers a diffusion theory that is **strictly weaker than quantum
mechanics**: it reproduces Madelung, not Schrödinger. Spending the gap-2
effort first risks building a derivation whose target is not QM.

**Recommendation:** attack (B) — Wallstrom — before or in parallel with gap 2,
and treat it as the gating question. It is cheaper (a topological/holonomy
question, not a new variational principle), it is sharply posed, it is
known-unresolved, and a negative answer would redirect the whole programme.

---

## Confidence

The assumes/concludes column is stated at a level I am confident of; I have
not re-derived any of it and assert no theorem numbers or precise hypotheses.
Wallstrom's objection and its status as unresolved I am confident of. The
`H^1`/ternary observation is my own suggestion, offered as a lead, **not** a
result — and it inherits the `\hbar` caveat above. Primary sources to check
before anything is built on this: Wallstrom (1994); Valentini (1991);
Gleason (1957); Busch (2003); Zurek (2005); Deutsch (1999) / Wallace;
Nelson (1966, 1985) and his own later reservations about locality.

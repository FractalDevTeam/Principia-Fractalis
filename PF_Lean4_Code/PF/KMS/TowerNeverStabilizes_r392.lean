/-
# r392: the substrate tower never stabilizes — "no end", formalized

★ 2026-10-30 r392 — the connecting maps are injective and never surjective ★

## Why this exists

Pablo's observation: a fractal has no beginning and no end, so the viewer is
always at the centre as far as the fractal is concerned. That is a statement
about the substrate, and it has two halves. This file proves one of them and
names the other.

**"No end" (upward).** Every level embeds in the next — injectively, by r386 —
and the embedding is **never onto**. So the tower strictly grows at every level,
forever: there is no level at which the structure closes up, and no level from
which the rest of the tower is redundant. That is the content below.

**"No beginning" (downward) — NOT proved here, and named precisely.** The
construction starts at level `0`, where `M_{3^0} = M_1(ℂ) = ℂ`. So *as written*
the substrate is a ray, not a line: it has a least level. The classical fact
that rescues the picture is the UHF **absorption identity**

    M_3(ℂ) ⊗ T_∞  ≅  T_∞

which says a factor can always be prepended, so `T_∞` contains a proper
subalgebra isomorphic to itself and has no bottom *up to isomorphism* even
though the construction has one. **That identity is absent from this corpus.**
It is the formal statement of "no beginning", it is the honest open target this
observation generates, and it needs the C\*-tensor machinery rather than the
algebraic direct limit used here.

## Why non-surjectivity is the right statement

Injectivity alone (r386) does not say the tower grows: an injective
endomorphism can be onto. What makes the tower a genuine fractal ray is that
each step adds something, at every step, with no largest step. Concretely,
`substrateEmbedMatrix k A = reindex (A ⊗ₖ 1₃)` has entries

    (A ⊗ₖ 1₃) (i,p) (j,q) = A i j · δ_{pq}

so **every matrix in the image vanishes off the `p = q` diagonal of the new
factor**. Any level-`(k+1)` matrix with a nonzero entry at `p ≠ q` — a matrix
unit coupling two different copies of the new `M_3` block — is outside the
image. The witness used below is exactly such a unit.

So the new factor is not decoration: it carries off-diagonal structure that no
earlier level can express. Each level is a strictly coarser view than the next,
from every level.

## What this says about the "viewer at the centre"

Combined: `ι_k` is injective (r386), the images are strictly increasing (here),
and every element of `T_∞` lies in some image (r359 `substrate_exhausted`). So
from any level the tower extends strictly upward without end and the whole limit
is reachable — no level is distinguished by anything intrinsic, and the only
asymmetry left is the floor at `k = 0`, which is precisely what the absorption
identity would remove.

**This is structural self-reference, not circular reasoning**, and the
distinction matters enough to state in the file: a fixed-point identity
`A ≅ M_3 ⊗ A` has content because UHF algebras are classified up to isomorphism
by their supernatural number, so the identity is a theorem with a uniqueness
statement behind it. An evidential loop — postulating the inputs a prediction is
then checked against — has no such backing. The substrate may be legitimately
self-similar while a dictionary built on top of it is illegitimately circular;
the two are independent, and the first does not license the second.

## What is NOT claimed

Not claimed: the absorption identity (see above). Not claimed: that `T_∞` has no
least level — as constructed it does, and this file says so. Not claimed:
anything about the C\*-completion, about scale-invariance of any physical
prediction, or about the α-dictionary. Not claimed: that non-surjectivity is
deep — it is a two-line entry count. Its value is that it was missing, and that
"the tower strictly grows" was being used informally without it.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-30.
-/
import PF.KMS.LevelMapInjective_r386

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped Kronecker
open PrincipiaTractalis.SubstrateBase3Embed
open PrincipiaTractalis.SubstrateBase3RingHom

/-! ## §1 — A level-`(k+1)` matrix outside the image

The witness: a unit coupling two distinct copies of the new `M_3` factor. Any
element of the image is `δ_{pq}`-diagonal in that factor, so this is not one. -/

/-- The off-diagonal witness, before reindexing: a single `1` at
`((0,0), (0,1))`. -/
noncomputable def offDiagWitness (k : ℕ) :
    Matrix (Fin (3^k) × Fin 3) (Fin (3^k) × Fin 3) ℂ :=
  fun u v => if u = (0, 0) ∧ v = (0, 1) then 1 else 0

/-- **★★★ r392: the substrate embedding is never onto ★★★**

So the tower strictly grows at every level: no level expresses the next. -/
theorem substrateEmbedMatrix_not_surjective (k : ℕ) :
    ¬ Function.Surjective (substrateEmbedMatrix k) := by
  intro hsurj
  obtain ⟨A, hA⟩ := hsurj
    (Matrix.reindex (levelStepEquiv k) (levelStepEquiv k) (offDiagWitness k))
  -- strip the reindexing, which is an equivalence
  have hker : A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) = offDiagWitness k :=
    (Matrix.reindex (levelStepEquiv k) (levelStepEquiv k)).injective hA
  -- read off the `(0,0),(0,1)` entry
  have hentry := congrFun (congrFun hker (0, 0)) (0, 1)
  have h01 : (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 1 = 0 :=
    Matrix.one_apply_ne (by decide)
  simp only [offDiagWitness, Matrix.kronecker_apply, h01, mul_zero,
    and_self, if_pos] at hentry
  exact absurd hentry (by norm_num)

/-- The bundled `RingHom` is likewise never onto. -/
theorem substrateRingHom_not_surjective (k : ℕ) :
    ¬ Function.Surjective (substrateRingHom k) :=
  substrateEmbedMatrix_not_surjective k

/-! ## §2 — Injective and not surjective, at every level

The pair is the point: injectivity alone would permit the tower to close up. -/

/-- **★ r392: every level is a strictly coarser view than the next ★** -/
theorem substrate_level_step_injective_not_surjective (k : ℕ) :
    Function.Injective (substrateRingHom k)
      ∧ ¬ Function.Surjective (substrateRingHom k) :=
  ⟨substrateRingHom_injective k, substrateRingHom_not_surjective k⟩

/-- **★ r392: the tower never stabilizes ★**

There is no level beyond which the embeddings become onto — the statement holds
at every `k`, so no tail of the tower is redundant. -/
theorem substrate_tower_never_stabilizes :
    ∀ k : ℕ, ¬ Function.Surjective (substrateRingHom k) :=
  substrateRingHom_not_surjective

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.offDiagWitness
#print axioms PF.KMS.substrateEmbedMatrix_not_surjective
#print axioms PF.KMS.substrateRingHom_not_surjective
#print axioms PF.KMS.substrate_level_step_injective_not_surjective
#print axioms PF.KMS.substrate_tower_never_stabilizes

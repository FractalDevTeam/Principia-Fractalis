/-
# r373: the same KMS structure on the NET — the tower's other presentation

★ 2026-10-28 r373 — one tower, three names ★

## Pablo's observation, made precise

The substrate tower appears in this corpus **three times**, under different
names, from different perspectives:

| presentation | carrier | colimit statement |
|---|---|---|
| direct limit over `ℕ` | `TimelessFieldRing` | `DirectLimit`, `of` |
| increasing union of subalgebras | `substrateTFCtower` | `substrateTFCtower_mono` + `_dense` (`SubstrateRigidity:441,470`) |
| **net over site sets** | `regionAlgebra ι S` | `net_eq_iSup_finite` (r354:234) |

r363–r372 built the KMS structure on the first. This file carries it to the
**third**, which is the one the Haag–Kastler axioms are stated about — and it
costs almost nothing, because r358 already proved the two are the same:

    netAlgEquivLevel k : Net k ≃ₐ[ℂ] Level k

is an **algebra** equivalence (that was exactly r358's upgrade over r357's
merely linear one), and `Level k` is literally `Matrix (Fin (3^k)) (Fin (3^k)) ℂ`
— the same object r363's `modularAut` acts on. So the dynamics transports by
conjugation, and every algebraic property comes with it.

That is the content of "the tower applies almost identically from a different
perspective, using different names": not an analogy, a proved identification.

## What is proved

* `netModularAut` — the modular automorphism acting on `Net k`, by conjugating
  `modularAut` through `netAlgEquivLevel`;
* `netModularAut_mul`, `netModularAut_one` — it is a unital multiplicative map
  on the net, i.e. an algebra endomorphism, inheriting r363's properties;
* `netGibbsFunctional` — the Gibbs functional read on the net;
* **`netGibbs_kms`** — the KMS identity **on the net**:
  `ω(u·v) = ω(v · σ(u))`;
* `netModularAut_of_scalar` — a scalar weight gives the identity on the net
  too, so the `β = 0`/tracial degeneration (r363, r366) survives the transport.

## Why the net side is the interesting one

The five proved Haag–Kastler axioms (r350–r354) are statements about
`regionAlgebra`. The missing sixth is **covariance**, which asks for a group
acting on the net. A one-parameter family of net automorphisms is the right
*shape* for that, and this file supplies net automorphisms where before there
were none.

**It is not covariance, and I am not claiming it is.** Covariance requires the
action to move *regions* — some `σ_t(𝒜(S)) = 𝒜(g_t S)` — and nothing here says
`netModularAut` relates `regionAlgebra S` to any region at all. What would make
it net-theoretic is a localisation statement: if the weight lies in
`regionAlgebra S`, then by locality (r351/r352) it commutes with
`regionAlgebra T` for `T` disjoint from `S`, so the modular automorphism should
act as the **identity** on `𝒜(T)`. That is a genuine and provable-looking
statement about this construction, it is **not proved here**, and it is the
right next target on this side.

## What is NOT claimed

Not claimed: covariance, any statement relating `netModularAut` to regions, the
descent of the net automorphisms to the net colimit `𝒜(ι)` (the analogue of
r372 on this side), positivity or state-ness on the net beyond what transports
from r364, or anything about `Out(T_∞)`.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.ModularAutomorphismFiniteLevel_r363
import PF.TernaryNetMatrixAlgBridge_r358

set_option autoImplicit false

namespace PF.KMS

open Matrix
open PrincipiaTractalis.TernaryNetMatrixBridge
open PrincipiaTractalis.TernaryNetMatrixAlgBridge

variable {k : ℕ}

/-! ## §1 — The modular automorphism, on the net -/

/-- The modular automorphism of a weight `X`, acting on the **net** `Net k` by
conjugation through r358's algebra equivalence. -/
noncomputable def netModularAut (k : ℕ) (X : Level k) (u : Net k) : Net k :=
  (netAlgEquivLevel k).symm (modularAut X (netAlgEquivLevel k u))

lemma netModularAut_mul (X : Level k) (hX : IsUnit X.det) (u v : Net k) :
    netModularAut k X (u * v)
      = netModularAut k X u * netModularAut k X v := by
  simp only [netModularAut, map_mul, modularAut_mul X hX]

lemma netModularAut_one (X : Level k) (hX : IsUnit X.det) :
    netModularAut k X (1 : Net k) = 1 := by
  simp only [netModularAut, map_one, modularAut_one X hX]

/-! ## §2 — The KMS identity, on the net -/

/-- The Gibbs functional, read on the net. -/
noncomputable def netGibbsFunctional (k : ℕ) (X : Level k) (u : Net k) : ℂ :=
  gibbsFunctional X (netAlgEquivLevel k u)

/-- **★★★ r373: the KMS identity on the Haag–Kastler net ★★★**

`ω(u·v) = ω(v · σ(u))`, with everything living on `Net k`. The proof is r363's
identity pushed through an algebra equivalence — which is why r358's upgrade
from linear to algebra mattered. -/
theorem netGibbs_kms (X : Level k) (hX : IsUnit X.det) (u v : Net k) :
    netGibbsFunctional k X (u * v)
      = netGibbsFunctional k X (v * netModularAut k X u) := by
  simp only [netGibbsFunctional, netModularAut, map_mul,
    AlgEquiv.apply_symm_apply]
  exact gibbs_kms X hX _ _

/-! ## §3 — The tracial degeneration survives the transport -/

/-- A scalar weight gives the identity on the net as well: the `β = 0` /
tracial case is trivial on both presentations, as it must be. -/
theorem netModularAut_of_scalar (c : ℂ) (hc : c ≠ 0) (u : Net k) :
    netModularAut k (c • (1 : Level k)) u = u := by
  simp only [netModularAut, modularAut_of_scalar c hc,
    AlgEquiv.symm_apply_apply]

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.netModularAut_mul
#print axioms PF.KMS.netModularAut_one
#print axioms PF.KMS.netGibbs_kms
#print axioms PF.KMS.netModularAut_of_scalar

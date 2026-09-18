/-
# O-CIRC: mechanical premise audit.

★ 2026-09-18 — discharges the "mechanical, not editorial" clause of obligation
O-CIRC (`codex/UNIFIED_THEORY_PROOF_PROGRAM.md` §3.1). ★

§3.1 requires that every premise of a candidate central theorem be checked
against its conclusion for definitional containment, **mechanically**. Until now
the check was a reading task. r337 is the argument for why that is not enough: a
dead hypothesis sat in `Substrate3Inf`, the premise of the project's central
theorem, and was found only by reading 2467 lines by hand.

This file provides `#audit_premises f`, a command that reports:

* **DEAD** — a field of a structure-valued hypothesis that the proof never
  consumes, transitively. This is the r337 finding, automated.
* **VACUOUS** — a hypothesis or field whose type reduces to `True`, i.e. one
  that can be discharged by `trivial` and therefore assumes nothing.
* **CONTAINED** — a hypothesis definitionally equal to the conclusion or to one
  of its conjuncts. This is the `D2`/`D3`/`D5` failure mode recorded in
  `UNIFICATION_COUNTERMODEL_LEDGER.md:57-62`, where advertised discharges are
  `rfl` identities returning their own inputs.

## Why the analysis must be transitive

`T_infinity_rigidity` has the one-line proof
`substrate3Inf_iso h substrate3Inf_TimelessFieldCompletion`. Every actual use of
the hypothesis fields happens further down, inside `substrate_forward_map` and
its dependencies. A shallow scan of the proof term would report *every* field
dead — the opposite of the truth. So the collector walks the call graph of the
proof, unfolding every constant whose name lies under a configurable namespace
prefix (default `PrincipiaTractalis`) and stopping at the mathlib boundary.

## What this does NOT do

* It does not prove a flagged premise is removable. DEAD means "no proof in the
  analysed cone mentions it"; removing it is still a human edit that must
  rebuild. r337 is the worked example of that second step.
* Descent stops at the namespace boundary, so a field consumed *only* inside a
  mathlib lemma specialised to it would be missed. In this corpus the substrate
  predicates are project-local, so the boundary is safe here; it is not safe in
  general and the report says so.
* CONTAINED uses `isDefEq` at default transparency. It finds `rfl`-identity
  circularity. It does not find semantic circularity that needs real reasoning.
-/

import Lean
import Mathlib.Tactic

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

namespace PF.Audit

/-- The user-facing name of a constant. Lean mangles `private` declarations to
    `_private.<module>.<n>.<realName>`, so a naive namespace test skips every
    private lemma. In `SubstrateRigidity` the entire C4 Elliott back-and-forth is
    private, and missing it made the first version of this auditor report every
    field dead — the exact opposite of the truth. -/
def userFacing (n : Name) : Name := (privateToUserName? n).getD n

/-- Every `Expr.proj` occurring in `e`, as `(structureName, fieldIndex)`. -/
partial def collectProjs : Expr → Array (Name × Nat) → Array (Name × Nat)
  | .proj s i b, acc => collectProjs b (acc.push (s, i))
  | .app f a,    acc => collectProjs a (collectProjs f acc)
  | .lam _ t b _, acc => collectProjs b (collectProjs t acc)
  | .forallE _ t b _, acc => collectProjs b (collectProjs t acc)
  | .letE _ t v b _, acc => collectProjs b (collectProjs v (collectProjs t acc))
  | .mdata _ b,  acc => collectProjs b acc
  | _,           acc => acc

/-- The transitive cone of a proof term: every constant name and every structure
    projection reachable by unfolding constants under `prefixes`. -/
partial def cone (env : Environment) (prefixes : Array Name) (fuel : Nat)
    (todo : List Name) (seen : NameSet) (consts : NameSet)
    (projs : Array (Name × Nat)) : NameSet × Array (Name × Nat) :=
  match fuel, todo with
  | 0, _ => (consts, projs)
  | _, [] => (consts, projs)
  | fuel+1, n :: rest =>
    if seen.contains n then
      cone env prefixes fuel rest seen consts projs
    else
      let seen := seen.insert n
      match env.find? n with
      | none => cone env prefixes fuel rest seen consts projs
      | some ci =>
        let body := ci.value?.getD default
        let consts := body.foldConsts consts (fun m s => s.insert m)
        let projs := collectProjs body projs
        -- also look at the TYPE, so field uses inside statements are counted
        let consts := ci.type.foldConsts consts (fun m s => s.insert m)
        let projs := collectProjs ci.type projs
        let next := body.foldConsts ([] : List Name) (fun m acc =>
          if prefixes.any (fun p => p.isPrefixOf (userFacing m)) && !seen.contains m
          then m :: acc else acc)
        cone env prefixes fuel (next ++ rest) seen consts projs

/-- Is `t` reducibly `True`? -/
def isTrivialProp (t : Expr) : MetaM Bool := do
  let t ← whnf t
  return t.isConstOf ``True

/-- Split a conclusion into conjuncts. -/
partial def conjuncts (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``And, #[a, b]) => return (← conjuncts a) ++ (← conjuncts b)
  | _ => return #[e]

/-- Every leaf field type reachable from a hypothesis `x`, recursing into
    structure-valued fields up to `depth`. Returns `(accessPath, fieldType)`.

    Needed because §3.1's circularity is not at the top level: `r301` takes one
    bundle `h`, and the containment lives at `h.bulletproof.rh_hp_program_positive`. -/
partial def leafFields (x : Expr) (path : String) (depth : Nat) :
    MetaM (Array (String × Expr)) := do
  if depth == 0 then return #[(path, ← inferType x)]
  let env ← getEnv
  let ty ← whnf (← inferType x)
  match ty.getAppFn with
  | .const s _ =>
    if isStructure env s then
      let mut out : Array (String × Expr) := #[]
      for f in getStructureFields env s do
        let some proj ← (do
            try pure (some (← mkAppM (s ++ f) #[x])) catch _ => pure none)
          | continue
        out := out ++ (← leafFields proj (path ++ "." ++ f.toString) (depth - 1))
      return out
    else return #[(path, ty)]
  | _ => return #[(path, ty)]

/-- `#audit_premises foo` — mechanical O-CIRC report for the declaration `foo`. -/
syntax (name := auditPremises) "#audit_premises " ident (ppSpace ident)? : command

@[command_elab auditPremises]
def elabAuditPremises : CommandElab := fun stx => do
  let declId := stx[1]
  let nsPrefix : Name :=
    if stx[2].isNone then `PrincipiaTractalis
    else stx[2][0].getId
  let declName ← liftCoreM <| realizeGlobalConstNoOverload declId
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "#audit_premises: unknown declaration {declName}"
  let some val := ci.value?
    | throwError "#audit_premises: {declName} has no value (axiom or opaque)"
  let (consts, projs) :=
    cone env #[nsPrefix] 20000 [declName] {} ({} : NameSet) #[]
  let _ := val
  liftTermElabM do
    forallTelescope ci.type fun xs concl => do
      let csRaw ← conjuncts concl
      -- dedup conjuncts up to defeq: the r301 conclusion repeats RH several
      -- times, which would otherwise multiply every finding
      let mut cs : Array Expr := #[]
      for c in csRaw do
        let mut dup := false
        for d in cs do
          if ← isDefEq c d then dup := true
        unless dup do cs := cs.push c
      let mut findings : Array MessageData := #[]
      for x in xs do
        let xty ← inferType x
        -- VACUOUS: the hypothesis itself assumes nothing
        if ← isTrivialProp xty then
          findings := findings.push m!"  VACUOUS   hypothesis : {xty}"
        -- CONTAINED: hypothesis is defeq to the conclusion or a conjunct
        for c in cs do
          if ← isDefEq xty c then
            findings := findings.push
              m!"  CONTAINED hypothesis is definitionally a conjunct of the conclusion:\n            {xty}"
        -- DEAD / VACUOUS fields of a structure-valued hypothesis
        let hty ← whnf xty
        if let .const sname _ := hty.getAppFn then
          if isStructure env sname then
            let fields := getStructureFields env sname
            for i in [:fields.size] do
              let f := fields[i]!
              let projName := sname ++ f
              let usedNamed := consts.contains projName
              let usedProj := projs.any (fun (s, j) => s == sname && j == i)
              if !usedNamed && !usedProj then
                findings := findings.push
                  m!"  DEAD      field never consumed in the proof cone: {projName}"
              else
                if let some fci := env.find? projName then
                  let ftyRes ← forallTelescope fci.type fun _ b => isTrivialProp b
                  if ftyRes then
                    findings := findings.push m!"  VACUOUS   field reduces to True: {projName}"
      -- NESTED CONTAINMENT: walk into structure hypotheses and compare every
      -- leaf field type against every conjunct of the conclusion, both directly
      -- and through one step of modus ponens (the D5 pattern of §3.1).
      let mut leaves : Array (String × Expr) := #[]
      for x in xs do
        leaves := leaves ++ (← leafFields x ((← inferType x).getAppFn.constName?.getD `_).toString 3)
      for c in cs do
        for (p, t) in leaves do
          if ← isDefEq t c then
            findings := findings.push
              m!"  CONTAINED premise field is definitionally a conclusion conjunct:\n            {p}\n            {c}"
        -- modus ponens: some field is `A → c` and some other field is `A`
        for (p, t) in leaves do
          let t' ← whnf t
          if t'.isArrow then
            let ante := t'.bindingDomain!
            let conseq := t'.bindingBody!
            if ← isDefEq conseq c then
              for (q, u) in leaves do
                if q != p then
                  if ← isDefEq u ante then
                    findings := findings.push
                      m!"  CONTAINED conclusion conjunct follows from premises by modus ponens:\n            {q}  :  A\n            {p}  :  A → conjunct\n            conjunct : {c}"
      if findings.isEmpty then
        logInfo m!"O-CIRC audit of {declName}: CLEAN \
          ({consts.size} constants in cone, boundary = {nsPrefix})"
      else
        logWarning m!"O-CIRC audit of {declName}: {findings.size} finding(s)\n\
          {MessageData.joinSep findings.toList "\n"}\n\
          (cone: {consts.size} constants, boundary = {nsPrefix}; \
          DEAD means no proof under that boundary mentions the field)"

end PF.Audit

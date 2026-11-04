/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.IndCheck.Base

/-!
# InLean's inductive checker: the install stages

Twins of `Kernel/Inductives/SumInstall(F).lean`,
`StructInstallF.lean`, `BlockInstall(F).lean` and the projection-table
check of `BlockInstallF.lean`, over the stored block and InLean's core.

**The job's environment.**  con-leche's checked job conses what it has
checked onto its own index (`FEnv.push`): the formers, then the
constructors, then (in the recursor stage) rule-less and generated
recursors.  Here the job conses the generator's constants of the same
names (`Job.push`), at the type the job checked them at (a def-headed
former at its reduced telescope, as con-leche's option C), and the core
reads them as it reads any Lean constant (its install-derived data,
`Lean/Kernel/InLean/Derived.lean`, come from those).  Every environment transition
drops the memos (`flush`, con-leche's `flushC`).  Projection tables are
not pushed: InLean reads them on use; their checks run.
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

namespace IC

/-- The checked job's fixed data: the mode, the core's `addConst`, the
generator's constants by name. -/
structure Job where
  μ : CheckMode
  addConst : Kernel.Environment → ConstantInfo → Kernel.Environment
  gen : Std.HashMap Name ConstantInfo

/-- con-leche's `CheckerOps` at an environment, on InLean's core. -/
def Job.infer (j : Job) (env : Kernel.Environment) (d : Nat) (e : Expr) : M Expr :=
  withReader (fun c => { c with env }) (InLean.infer j.μ d e)
def Job.defeq (j : Job) (env : Kernel.Environment) (d : Nat) (a b : Expr) : M Bool :=
  withReader (fun c => { c with env }) (InLean.defeq j.μ d a b)
def Job.ensureSort (j : Job) (env : Kernel.Environment) (d : Nat) (e : Expr) : M Level :=
  withReader (fun c => { c with env }) (InLean.ensureSort j.μ d e)
def Job.whnf (j : Job) (env : Kernel.Environment) (d : Nat) (e : Expr) : M Expr :=
  withReader (fun c => { c with env }) (InLean.whnf j.μ d e)
/-- con-leche's `checkConstantValF` (InLean's `checkConstantVal`). -/
def Job.checkConstantVal (j : Job) (env : Kernel.Environment) (cv : CV) : M Unit :=
  withReader (fun c => { c with env }) (InLean.checkConstantVal j.μ cv.name cv.lps cv.type)

/-- con-leche's `flushC`. -/
def flush : M Unit := Ind.flushAllMemos

/-- Cons the generator's constant `n`, at the type `ty` the job checked
(the job's `FEnv.push`); a recursor with the rules given. -/
def Job.push (j : Job) (env : Kernel.Environment) (n : Name) (ty : Expr)
    (rules? : Option (List RecursorRule) := none) : M Kernel.Environment := do
  match j.gen[n]? with
  | some (.inductInfo v) => return j.addConst env (.inductInfo { v with type := ty })
  | some (.ctorInfo v) => return j.addConst env (.ctorInfo { v with type := ty })
  | some (.recInfo v) =>
    return j.addConst env (.recInfo { v with type := ty, rules := rules?.getD [] })
  | _ => throwInternal s!"inductive checker: no generated constant {n}"

/-! ## Telescopes and field sorts (twin of `SumInstall.lean`) -/

/-- Twin of `whnfTelescope`. -/
def whnfTelescope (j : Job) (env : Kernel.Environment) : Nat → Nat → Expr → M (List Expr × Level)
  | i, 0, e => do
    match ← j.whnf env i e with
    | .sort s => pure ([], s)
    | _ => throwInvalid "direct sum: type former does not reduce to a sort after its parameters \
        and indices"
  | i, n + 1, e => do
    match ← j.whnf env i e with
    | .forallE _ dom body _ =>
      let (bs, s) ← whnfTelescope j env (i + 1) n (body.inst1I (← fvar i dom))
      pure (dom :: bs, s)
    | _ => throwInvalid "direct sum: type former does not reduce to a telescope of its \
        parameters and indices"

/-- Twin of `checkSumTeleF`. -/
def checkSumTele (j : Job) (env : Kernel.Environment) (cv : CV) (n : Nat) (cvTa₀ : CV) :
    M (CV × Level) := do
  match stripPis n cvTa₀.type with
  | some (_, .sort s) => pure (cvTa₀, s)
  | _ =>
    let (bs, s) ← whnfTelescope j env 0 n cvTa₀.type
    let cvTa := { cv with type := ← closeTelescope bs 0 (.sort s) }
    j.checkConstantVal env cvTa
    pure (cvTa, s)

/-- Twin of `checkStructFieldSortsIFA`. -/
def checkStructFieldSorts (j : Job) (env : Kernel.Environment) (isProp large : Bool) (s : Level)
    (nP : Nat) (fvs : Array Expr) (idxArgs : List Expr) : Nat → M (List Level)
  | 0 => pure []
  | k + 1 => do
    let fv ← unwrapOr fvs[k]? (.internal "direct sum: field index")
    let ty ← j.infer env (nP + k) (← fvarTypeD fv)
    let u ← j.ensureSort env (nP + k) ty
    if !isProp then
      unless ← liftLevel (Lvl.leq u s) do throwInvalid "direct sum: field universe too large"
    else if large then
      unless Lvl.isZero u || idxArgs.contains fv do
        throwInvalid "direct sum: large eliminator with a non-propositional field outside the \
          indices"
    let rest ← checkStructFieldSorts j env isProp large s nP fvs idxArgs k
    pure (rest ++ [u])

/-- Twin of `checkStructDomsAtFA`. -/
def checkStructDomsAt (j : Job) (env : Kernel.Environment) (off : Nat) (fvs doms : Array Expr) :
    Nat → M Unit
  | 0 => pure ()
  | k + 1 => do
    let a ← unwrapOr fvs[k]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[k]? (.internal "direct structure: domain index")
    unless ← j.defeq env (off + k) (← fvarTypeD a) b do
      throwDeclined "direct structure: binder domain mismatch"
    checkStructDomsAt j env off fvs doms k

/-- Twin of `structPsAt`. -/
def structPsAt (o nP : Nat) : List Expr := (List.range nP).map fun k => .bvar (o + nP - 1 - k)

/-- Twin of `structCtorResidOk`. -/
def structCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool :=
  cbody.getAppFn == .const T (lps.map .param) &&
  cbody.getAppNumArgs == nP + nIdx &&
  cbody.getAppArgs.toList.take nP == structPsAt o nP

/-- Twin of `checkSumCtorF`. -/
def checkSumCtor (j : Job) (env₀ env : Kernel.Environment) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvC : CV) (nF : Nat) (cvTa : CV) :
    M (CV × List Level) := do
  j.checkConstantVal env cvC
  let (_, cbody) ← unwrapOr (stripPis (nP + nF) cvC.type)
    (.declined "direct sum: constructor telescope")
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throwInvalid "direct sum: invalid constructor return type"
  let cq ← unwrapOr (← openPis nP cvC.type 0) (.declined "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPis nP cvTa.type 0) (.declined "direct sum: type former telescope")
  let tdoms ← tq.1.toArray.mapM fvarTypeD
  checkStructDomsAt j env 0 cq.1.toArray tdoms nP
  let xq ← unwrapOr (← openPis nF cq.2 nP) (.declined "direct sum: constructor field telescope")
  let rargs := xq.2.getAppArgs.toList
  unless xq.2.getAppFn == .const T (lps.map .param) && rargs.take nP == cq.1 &&
      rargs.length == nP + nIdx do
    throwDeclined "direct sum: opened constructor residual"
  for x in xq.1 do
    unless ← constsResolve env₀ (← fvarTypeD x) do
      throwDeclined "direct sum: field domain after the block"
  for e in rargs.drop nP do
    unless ← constsResolve env₀ e do
      throwInvalid "direct sum: index expression mentions the block"
  let sorts ← checkStructFieldSorts j env isProp large resSort nP xq.1.toArray (rargs.drop nP) nF
  pure (cvC, sorts)

/-- Twin of `checkSumCtorsF`. -/
def checkSumCtors (j : Job) (env₀ env : Kernel.Environment) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvTa : CV) :
    List (CV × Nat) → M (List (CV × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let (cvCa, sorts) ← checkSumCtor j env₀ env T lps nP nIdx resSort isProp large c.1 c.2 cvTa
    let (rest, srest) ← checkSumCtors j env₀ env T lps nP nIdx resSort isProp large cvTa cs
    pure ((cvCa, c.2) :: rest, sorts :: srest)

/-! ## The block's formers, constructors and index sorts (twin of `BlockInstallF.lean`) -/

/-- Twin of `checkBlockTeleF`. -/
def checkBlockTele (j : Job) (env : Kernel.Environment) (nP : Nat) (ms : MemberShape) :
    M (CV × Level) := do
  j.checkConstantVal env ms.cvT
  let (cvTa, s) ← checkSumTele j env ms.cvT (nP + ms.nIdx) ms.cvT
  let (_, tbody) ← unwrapOr (stripPis (nP + ms.nIdx) cvTa.type)
    (.internal "direct sum: type former telescope")
  unless tbody == .sort s do throwInternal "direct sum: type former result sort"
  pure (cvTa, s)

/-- Twin of `checkBlockDomsAtF`. -/
def checkBlockDomsAt (j : Job) (env : Kernel.Environment) (off : Nat) (fvs doms : List Expr) :
    Nat → M Unit
  | 0 => pure ()
  | k + 1 => do
    let a ← unwrapOr fvs[k]? (.internal "block: domain index")
    let b ← unwrapOr doms[k]? (.internal "block: domain index")
    unless ← j.defeq env (off + k) (← fvarTypeD a) b do
      throwInvalid "parameters of all inductive datatypes must match"
    checkBlockDomsAt j env off fvs doms k

/-- Twin of `checkBlockAgreeF`. -/
def checkBlockAgree (j : Job) (env : Kernel.Environment) (nP : Nat) (cvTa0 : CV) (s0 : Level) :
    List (CV × Level) → M Unit
  | [] => pure ()
  | (cvTa, s) :: rest => do
    let tq0 ← unwrapOr (← openPis nP cvTa0.type 0) (.internal "block: type former telescope")
    let tq ← unwrapOr (← openPis nP cvTa.type 0)
      (.invalid "parameters of all inductive datatypes must match")
    unless tq.1.length == tq0.1.length do
      throwInvalid "parameters of all inductive datatypes must match"
    checkBlockDomsAt j env 0 tq.1 (← tq0.1.mapM fvarTypeD) nP
    unless ← isEquivL s s0 do throwInvalid "mutually inductive types must live in the same universe"
    checkBlockAgree j env nP cvTa0 s0 rest

/-- Twin of `checkBlockIndsF`: the formers checked and consed. -/
def checkBlockInds (j : Job) (env : Kernel.Environment) (p : BlockShape) :
    M (Kernel.Environment × List CV × BlockShape) := do
  match p.members with
  | [] => throwInternal "block: no type former"
  | ms0 :: rest =>
    let (cvTa0, s0) ← checkBlockTele j env p.nP ms0
    let mut cvs : List (CV × Level) := []
    for ms in rest do
      cvs := cvs ++ [← checkBlockTele j env p.nP ms]
    checkBlockAgree j env p.nP cvTa0 s0 cvs
    let p₁ := p.withSort s0
    let cvTas := cvTa0 :: cvs.map (·.1)
    let mut env₁ := env
    for cvTa in cvTas do
      env₁ ← j.push env₁ cvTa.name cvTa.type
    pure (env₁, cvTas, p₁)

/-- Twin of `checkBlockCtorsF`. -/
def checkBlockCtors (j : Job) (env₀ env : Kernel.Environment) (p : BlockShape) :
    List (MemberShape × CV) → M (List (List (CV × Nat)) × List (List (List Level)))
  | [] => pure ([], [])
  | (ms, cvTa) :: rest => do
    let (ctorsA, sortss) ← checkSumCtors j env₀ env ms.cvT.name p.lps p.nP ms.nIdx p.resSort
      p.isProp p.large cvTa ms.ctors
    let (restC, restS) ← checkBlockCtors j env₀ env p rest
    pure (ctorsA :: restC, sortss :: restS)

/-- Twin of `checkBlockIdxSortsF`. -/
def checkBlockIdxSorts (j : Job) (env₁ : Kernel.Environment) (p : BlockShape) :
    List (MemberShape × CV) → M (List (List Level))
  | [] => pure []
  | (ms, cvTa) :: rest => do
    let tq ← unwrapOr (← openPis (p.nP + ms.nIdx) cvTa.type 0)
      (.internal "direct rec: type former telescope")
    let isorts ← checkStructFieldSorts j env₁ true false p.resSort p.nP (tq.1.drop p.nP).toArray []
      ms.nIdx
    let rest ← checkBlockIdxSorts j env₁ p rest
    pure (isorts :: rest)

/-- Twin of `consBlockCtorsF`. -/
def consBlockCtors (j : Job) (ctorsAs : List (List (CV × Nat))) (env : Kernel.Environment) :
    M Kernel.Environment := do
  let mut env := env
  for cs in ctorsAs do
    for c in cs do
      env ← j.push env c.1.name c.1.type
  return env

/-- Twin of `structProjGuards`. -/
def structProjGuards (cty : Expr) (nP nF : Nat) (sorts : List Level) : List Level :=
  let used (k : Nat) : Bool := match stripPis (nP + k + 1) cty with
    | some (_, rest) => rest.hasLooseBVarI 0
    | none => false
  (List.range nF).map fun i =>
    (List.range i).foldl (fun acc k => if used k then .max acc (sorts.getD k .zero) else acc)
      (sorts.getD i .zero)

/-- Twin of `checkStructProjTableF`'s checks (the table itself is read on
use, `projTableOf`). -/
def checkStructProjTable (env : Kernel.Environment) (T : Name) (lps : List Name) (nP nF : Nat)
    (cvCa : CV) : M Unit := do
  let bodies ← unwrapOr (structProjBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  unless bodies.size == nF do throwInternal "direct structure: projection body scoping"
  for b in bodies do
    unless !b.hasFVar && (← allLevelParamsDefined lps b) && (← constsResolve env b) &&
        b.looseBVarRange ≤ nP + 1 do
      throwInternal "direct structure: projection body scoping"
  unless (env.find? T).isSome do
    throwInternal "direct structure: projection table before its structure"

/-- Twin of `checkBlockTablesF`. -/
def checkBlockTables (p : BlockShape) (env : Kernel.Environment) :
    List (MemberShape × List (CV × Nat) × List (List Level)) → M Unit
  | [] => pure ()
  | (ms, ctorsA, sortss) :: rest => do
    match ctorsA, sortss with
    | [cA], [_] =>
      if ms.nIdx == 0 then checkStructProjTable env ms.cvT.name p.lps p.nP cA.2 cA.1
    | _, _ => pure ()
    checkBlockTables p env rest

end IC

end Lean.Kernel.InLean

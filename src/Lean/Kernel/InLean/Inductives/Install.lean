/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude

public import Lean.Kernel.InLean.Inductives.BlockShape
public import Lean.Kernel.InLean.Push

/-!
# InLean's inductive check: the formers, the constructors, the tables

Twins of the executed stages of `ConLeche/Kernel/Inductives/SumInstall.lean`,
`SumInstallF.lean`, `StructParts.lean`, `StructInstallF.lean`,
`BlockInstall.lean` and `BlockInstallF.lean`, and of
`ConLeche/Kernel/DeclCheck.lean`'s `checkConstantValF`.

An environment push records a Lean entry: a former as an `InductiveVal`
whose `all`, counts, constructors and `isRec` are the block's (what
`blockCapsAt` stores, read back by `FEnv.indView?`), a constructor as a
`ConstructorVal` with its counts, a rule-less recursor as a `RecursorVal`
whose counts encode `(mI, rP)` (`numParams := rP`, `numIndices := mI - rP`).
-/

@[expose] public section

namespace Lean.Kernel.InLean

open Lean

/-- Twin of `checkConstantValF`. -/
def checkConstantValF (ops : CheckerOps) (fe : FEnv) (cv : ConstantVal) (allowOp : Bool := false) :
    CheckCM Unit := do
  if (fe.find? cv.name).isSome then throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then throw (.invalid s!"reserved basis name {cv.name}")
  if natOpName cv.name && !allowOp && !fe.coreAxioms then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk cv.name cv.levelParams cv.type do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless namesNodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  checkTermWF fe s!"type of {cv.name}" cv.levelParams cv.type
  let stype ← ops.inferType fe 0 cv.type
  let _u ← ops.ensureSort fe 0 stype

/-! ## Structure parts (twin of `StructParts.lean`) -/

/-- Twin of `structPsAt`. -/
def structPsAt (o nP : Nat) : List Expr :=
  (List.range nP).map fun k => .bvar (o + nP - 1 - k)

/-- Twin of `structElimLevel`. -/
def structElimLevel (elim : Name) (large : Bool) : Level :=
  if large then .param elim else .zero

/-- Twin of `structCtorResidOk`. -/
def structCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool :=
  cbody.getAppFn == .const T (lps.map .param) &&
  cbody.getAppNumArgs == nP + nIdx &&
  (appArgs cbody).take nP == structPsAt o nP

/-- Twin of `Expr.mentionsConst`. -/
def mentionsConst (T : Name) (e : Expr) : CheckCM Bool := mentionsAnyConst [T] e

/-! ## Sums (twins of `SumInstall.lean`, `SumInstallF.lean`) -/

/-- Twin of `checkSumTele`. -/
def checkSumTele (n : Nat) (cvTa₀ : ConstantVal) : CheckCM (ConstantVal × Level) :=
  match stripPis n cvTa₀.type with
  | some (_, .sort s) => pure (cvTa₀, s)
  | _ => throw (.invalid "direct sum: type former does not reduce to a sort after its \
      parameters and indices")

/-- Twin of `checkStructFieldSortsIF`. -/
def checkStructFieldSortsIF (ops : CheckerOps) (fe : FEnv) (isProp large : Bool) (s : Level)
    (nP : Nat) (fvs idxArgs : List Expr) : Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType fe (nP + j) (← fvarTypeD fv)
    let u ← ops.ensureSort fe (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Lvl.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Lvl.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    checkStructFieldSortsIF ops fe isProp large s nP fvs idxArgs j

/-- Twin of `checkStructDomsAtFA` (on lists). -/
def checkStructDomsAtF (ops : CheckerOps) (fe : FEnv) (off : Nat) (fvs doms : List Expr) :
    Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe (off + j) (← fvarTypeD a) b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAtF ops fe off fvs doms j

/-- Twin of `checkSumCtorF`. -/
def checkSumCtorF (ops : CheckerOps) (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    CheckCM Unit := do
  checkConstantValF ops fe cvC
  let (_, cbody) ← unwrapOr (stripPis (nP + nF) cvC.type)
    (.notImplemented "direct sum: constructor telescope")
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "direct sum: invalid constructor return type")
  let cq ← unwrapOr (← openPisAtFvars nP cvC.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (← openPisAtFvars nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAtF ops fe 0 cq.1 (← tq.1.mapM fvarTypeD) nP
  let xq ← unwrapOr (← openPisAtFvars nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      (appArgs xq.2).take nP == cq.1 && xq.2.getAppNumArgs == nP + nIdx do
    throw (.notImplemented "direct sum: opened constructor residual")
  let fieldsOk ← xq.1.allM fun x => do constsResolveF fe₀ (← fvarTypeD x)
  unless fieldsOk do
    throw (.notImplemented "direct sum: field domain after the block")
  unless ← ((appArgs xq.2).drop nP).allM (constsResolveF fe₀) do
    throw (.invalid "direct sum: index expression mentions the block")
  checkStructFieldSortsIF ops fe isProp large resSort nP xq.1 ((appArgs xq.2).drop nP) nF

/-- Twin of `checkSumCtorsF`. -/
def checkSumCtorsF (ops : CheckerOps) (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → CheckCM Unit
  | [] => pure ()
  | c :: cs => do
    checkSumCtorF ops fe₀ fe T lps nP nIdx resSort isProp large c.1 c.2 cvTa
    checkSumCtorsF ops fe₀ fe T lps nP nIdx resSort isProp large cvTa cs

/-- Twin of `consSumCtorsF`: each constructor pushed with its counts (its
family `T` and its position recorded as Lean's entry has them). -/
def consSumCtorsF (T : Name) (nP : Nat) : Nat → List (ConstantVal × Nat) → FEnv → FEnv
  | _, [], fe => fe
  | i, c :: cs, fe =>
    consSumCtorsF T nP (i + 1) cs
      (fe.push (.ctorInfo { toConstantVal := c.1, induct := T, cidx := i, numParams := nP,
                            numFields := c.2, isUnsafe := false }))

/-! ## Structures (twin of `StructInstallF.lean`) -/

/-- Twin of `StructWalkers`. -/
structure StructWalkers where
  resolve : FEnv → Expr → CheckCM Bool
  projBodies : Name → Nat → Nat → Expr → Option (Array Expr)

/-- Twin of `StructWalkers.plain`. -/
def StructWalkers.plain : StructWalkers := ⟨constsResolveF, structProjBodies⟩

/-- Twin of `checkStructProjTableF`.  A projection table is read off its
structure (`FEnv.findProj?`), so the "table taken" refusal has nothing to
find: the structure's name is fresh (`checkConstantValF`). -/
def checkStructProjTableF (w : StructWalkers) (T : Name) (lps : List Name) (nP nF : Nat)
    (cvCa : ConstantVal) (fe : FEnv) : CheckCM Unit := do
  let bodies ← unwrapOr (w.projBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  unless bodies.size = nF ∧ (← bodies.allM fun b => do
      pure (!b.hasFVar) <&&> allLevelParamsDefined lps b <&&> w.resolve fe b <&&>
        pure (b.looseBVarRange ≤ nP + 1)) do
    throw (.internal "direct structure: projection body scoping")
  unless (fe.find? T).isSome do
    throw (.internal "direct structure: projection table before its structure")

/-! ## The block (twins of `BlockInstall.lean`, `BlockInstallF.lean`) -/

/-- Twin of `Expr.piDomsMentionAny`. -/
def piDomsMentionAny (names : List Name) : Expr → Bool
  | .forallE _ ty b _ =>
    EO.any (fun | .const n _ => names.contains n | .proj s _ _ => names.contains s | _ => false) ty ||
      piDomsMentionAny names b
  | _ => false

/-- Twin of `blockIsRec`. -/
def blockIsRec (p : BlockShape) : Bool :=
  p.members.any fun ms => ms.ctors.any fun c => piDomsMentionAny p.memberNames c.1.type

/-- Twin of `checkBlockTeleF`. -/
def checkBlockTeleF (ops : CheckerOps) (fe : FEnv) (nP : Nat) (ms : MemberShape) :
    CheckCM (ConstantVal × Level) := do
  checkConstantValF ops fe ms.cvT
  let (cvTa, s) ← checkSumTele (nP + ms.nIdx) ms.cvT
  let (_, tbody) ← unwrapOr (stripPis (nP + ms.nIdx) cvTa.type)
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do throw (.internal "direct sum: type former result sort")
  pure (cvTa, s)

/-- Twin of `checkBlockTelesF`. -/
def checkBlockTelesF (ops : CheckerOps) (fe : FEnv) (nP : Nat) :
    List MemberShape → CheckCM (List (ConstantVal × Level))
  | [] => pure []
  | ms :: rest => do
    let r ← checkBlockTeleF ops fe nP ms
    let rs ← checkBlockTelesF ops fe nP rest
    pure (r :: rs)

/-- Twin of `checkBlockDomsAtF`. -/
def checkBlockDomsAtF (ops : CheckerOps) (fe : FEnv) (off : Nat) (fvs doms : List Expr) :
    Nat → CheckCM Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "block: domain index")
    let b ← unwrapOr doms[j]? (.internal "block: domain index")
    unless ← ops.isDefEq fe (off + j) (← fvarTypeD a) b do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtF ops fe off fvs doms j

/-- Twin of `checkBlockAgreeF`. -/
def checkBlockAgreeF (ops : CheckerOps) (fe : FEnv) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    List (ConstantVal × Level) → CheckCM Unit
  | [] => pure ()
  | (cvTa, s) :: rest => do
    let tq0 ← unwrapOr (← openPisAtFvars nP cvTa0.type 0) (.internal "block: type former telescope")
    let tq ← unwrapOr (← openPisAtFvars nP cvTa.type 0)
      (.invalid "parameters of all inductive datatypes must match")
    unless tq.1.length == tq0.1.length do
      throw (.invalid "parameters of all inductive datatypes must match")
    checkBlockDomsAtF ops fe 0 tq.1 (← tq0.1.mapM fvarTypeD) nP
    unless ← liftFueled "level comparison" (Lvl.isEquiv s s0) do
      throw (.invalid "mutually inductive types must live in the same universe")
    checkBlockAgreeF ops fe nP cvTa0 s0 rest

/-- Twin of `consBlockIndsF`: each former pushed as the entry `blockCapsAt`
reads back (`all`, counts, constructors, `isRec`). -/
def consBlockIndsF (p₁ : BlockShape) (isRec : Bool) : List ConstantVal → Nat → FEnv → FEnv
  | [], _, fe => fe
  | cvTa :: rest, i, fe =>
    let ms := p₁.members.getD i default
    let v : InductiveVal :=
      { toConstantVal := cvTa
        numParams := p₁.nP
        numIndices := ms.nIdx
        all := p₁.memberNames
        ctors := ms.ctors.map (·.1.name)
        numNested := 0
        isRec := isRec
        isUnsafe := false
        isReflexive := false }
    consBlockIndsF p₁ isRec rest (i + 1) (fe.push (.inductInfo v))

/-- Twin of `checkBlockIndsF`. -/
def checkBlockIndsF (ops : CheckerOps) (fe : FEnv) (p : BlockShape) (isRec : Bool) :
    CheckCM (FEnv × BlockShape) :=
  match p.members with
  | [] => throw (.internal "block: no type former")
  | ms0 :: rest => do
    let (cvTa0, s0) ← checkBlockTeleF ops fe p.nP ms0
    let cvs ← checkBlockTelesF ops fe p.nP rest
    checkBlockAgreeF ops fe p.nP cvTa0 s0 cvs
    let p₁ := p.withSort s0
    pure (consBlockIndsF p₁ isRec (p.members.map (·.declared)) 0 fe, p₁)

/-- Twin of `checkBlockCtorsF`. -/
def checkBlockCtorsF (ops : CheckerOps) (fe₀ fe : FEnv) (p : BlockShape) :
    List MemberShape → CheckCM Unit
  | [] => pure ()
  | ms :: rest => do
    checkSumCtorsF ops fe₀ fe ms.cvT.name p.lps p.nP ms.nIdx p.resSort p.isProp p.large ms.cvT
      ms.ctors
    checkBlockCtorsF ops fe₀ fe p rest

/-- Twin of `checkBlockIdxSortsF`. -/
def checkBlockIdxSortsF (ops : CheckerOps) (fe₁ : FEnv) (p : BlockShape) :
    List MemberShape → CheckCM Unit
  | [] => pure ()
  | ms :: rest => do
    let tq ← unwrapOr (← openPisAtFvars (p.nP + ms.nIdx) ms.cvT.type 0)
      (.internal "direct rec: type former telescope")
    checkStructFieldSortsIF ops fe₁ true false p.resSort p.nP (tq.1.drop p.nP) [] ms.nIdx
    checkBlockIdxSortsF ops fe₁ p rest

/-- Twin of `consBlockCtorsF`. -/
def consBlockCtorsF (p : BlockShape) : FEnv → FEnv :=
  fun fe => p.members.foldl (fun fe ms => consSumCtorsF ms.cvT.name p.nP 0 ms.ctors fe) fe

/-- A recursor entry at `(mI, rP)`, its rules and K flag. -/
def recEntry (p : BlockShape) (cv : ConstantVal) (mI rP : Nat) (isK : Bool)
    (rules : List RecursorRule) : ConstantInfo :=
  .recInfo { toConstantVal := cv, all := p.memberNames, numParams := rP, numIndices := mI - rP,
                     numMotives := 0, numMinors := 0, rules, k := isK, isUnsafe := false }

/-- Twin of `consBlockRecsBareF`. -/
def consBlockRecsBareF (p : BlockShape) : Nat → List (ConstantVal × Nat) → FEnv → FEnv
  | _, [], fe => fe
  | m, (cvRa, _nIdx) :: rest, fe =>
    consBlockRecsBareF p (m + 1) rest
      (fe.push (recEntry p cvRa (p.majorIdxAt m) (p.rulePrefixAt m) false []))

/-- Twin of `checkBlockTablesF`. -/
def checkBlockTablesF (w : StructWalkers) (p : BlockShape) (fe : FEnv) :
    List MemberShape → CheckCM Unit
  | [] => pure ()
  | ms :: rest => do
    (match ms.structCtor? with
     | some c => checkStructProjTableF w ms.cvT.name p.lps p.nP c.2 c.1 fe
     | none => pure ())
    checkBlockTablesF w p fe rest

end Lean.Kernel.InLean

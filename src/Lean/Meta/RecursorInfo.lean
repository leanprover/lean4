/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.AuxRecursor
import Lean.Util.FindExpr
import Lean.Meta.Basic

namespace Lean.Meta

inductive RecursorUnivLevelPos where
  | motive                -- marks where the universe of the motive should go
  | majorType (idx : Nat) -- marks where the #idx universe of the major premise type goes

instance : ToString RecursorUnivLevelPos := ⟨fun
  | RecursorUnivLevelPos.motive        => "<motive-univ>"
  | RecursorUnivLevelPos.majorType idx => toString idx⟩

structure RecursorInfo where
  recursorName  : Name
  typeName      : Name
  univLevelPos  : List RecursorUnivLevelPos
  depElim       : Bool
  recursive     : Bool
  numArgs       : Nat -- Total number of arguments
  majorPos      : Nat
  paramsPos     : List (Option Nat) -- Position of the recursor parameters in the major premise, instance implicit arguments are `none`
  indicesPos    : List Nat -- Position of the recursor indices in the major premise
  produceMotive : List Bool -- If the i-th element is true then i-th minor premise produces the motive

namespace RecursorInfo

def numParams (info : RecursorInfo) : Nat := info.paramsPos.length
def numIndices (info : RecursorInfo) : Nat := info.indicesPos.length
def motivePos (info : RecursorInfo) : Nat := info.numParams
def firstIndexPos (info : RecursorInfo) : Nat := info.majorPos - info.numIndices

def isMinor (info : RecursorInfo) (pos : Nat) : Bool :=
  if pos ≤ info.motivePos then false
  else if info.firstIndexPos ≤ pos && pos ≤ info.majorPos then false
  else true

def numMinors (info : RecursorInfo) : Nat :=
  let r := info.numArgs
  let r := r - info.motivePos - 1
  r - (info.majorPos + 1 - info.firstIndexPos)

instance : ToString RecursorInfo := ⟨fun info =>
  "{\n" ++
  "  name           := " ++ toString info.recursorName ++ "\n" ++
  "  type           := " ++ toString info.typeName ++ "\n" ++
  "  univs          := " ++ toString info.univLevelPos ++ "\n" ++
  "  depElim        := " ++ toString info.depElim ++ "\n" ++
  "  recursive      := " ++ toString info.recursive ++ "\n" ++
  "  numArgs        := " ++ toString info.numArgs ++ "\n" ++
  "  numParams      := " ++ toString info.numParams ++ "\n" ++
  "  numIndices     := " ++ toString info.numIndices ++ "\n" ++
  "  numMinors      := " ++ toString info.numMinors ++ "\n" ++
  "  major          := " ++ toString info.majorPos ++ "\n" ++
  "  motive         := " ++ toString info.motivePos ++ "\n" ++
  "  paramsAtMajor  := " ++ toString info.paramsPos ++ "\n" ++
  "  indicesAtMajor := " ++ toString info.indicesPos ++ "\n" ++
  "  produceMotive  := " ++ toString info.produceMotive ++ "\n" ++
  "}"⟩

end RecursorInfo

private def getMajorPosIfAuxRecursor? (declName : Name) (majorPos? : Option Nat) : MetaM (Option Nat) :=
  if majorPos?.isSome then pure majorPos?
  else do
    let env ← getEnv
    if !isAuxRecursor env declName then pure none
    else match declName with
    | .str p s =>
      if s != recOnSuffix && s != casesOnSuffix && s != brecOnSuffix then
        pure none
      else do
        let val ← getConstInfoRec (mkRecName p)
        pure $ some (val.numParams + val.numIndices + (if s == casesOnSuffix then 1 else val.numMotives))
    | _ => pure none

private def checkMotive (declName : Name) (motive : Expr) (motiveArgs : Array Expr) : MetaM Unit :=
  unless motive.isFVar && motiveArgs.all Expr.isFVar do
    throwError "invalid user defined recursor '{declName}', result type must be of the form (C t), where C is a bound variable, and t is a (possibly empty) sequence of bound variables"

/-- Compute number of parameters for (user-defined) recursor.
   We assume a parameter is anything that occurs before the motive -/
private partial def getNumParams (xs : Array Expr) (motive : Expr) (i : Nat) : Nat :=
  if h : i < xs.size then
    if motive == xs[i] then i
    else getNumParams xs motive (i+1)
  else
    i

private def getMajorPosDepElim (declName : Name) (majorPos? : Option Nat) (xs : Array Expr) (motiveArgs : Array Expr)
    : MetaM (Expr × Nat × Bool) := do
  match majorPos? with
  | some majorPos =>
    if h : majorPos < xs.size then
      let major   := xs[majorPos]
      let depElim := motiveArgs.contains major
      pure (major, majorPos, depElim)
    else throwError "invalid major premise position for user defined recursor, recursor has only {xs.size} arguments"
  | none => do
    if motiveArgs.isEmpty then
      throwError "invalid user defined recursor, '{declName}' does not support dependent elimination, and position of the major premise was not specified (solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)"
    let major := motiveArgs.back!
    match xs.getIdx? major with
    | some majorPos => pure (major, majorPos, true)
    | none          => throwError "ill-formed recursor '{declName}'"

private def getParamsPos (declName : Name) (xs : Array Expr) (numParams : Nat) (Iargs : Array Expr) : MetaM (List (Option Nat)) := do
  let mut paramsPos := #[]
  for i in [:numParams] do
    let x := xs[i]!
    match (← Iargs.findIdxM? fun Iarg => isDefEq Iarg x) with
    | some j => paramsPos := paramsPos.push (some j)
    | none   => do
      let localDecl ← x.fvarId!.getDecl
      if localDecl.binderInfo.isInstImplicit then
        paramsPos := paramsPos.push none
      else
        throwError"invalid user defined recursor '{declName}', type of the major premise does not contain the recursor parameter"
  pure paramsPos.toList

private def getIndicesPos (declName : Name) (xs : Array Expr) (majorPos numIndices : Nat) (Iargs : Array Expr) : MetaM (List Nat) := do
  let mut indicesPos := #[]
  for i in [:numIndices] do
    let i := majorPos - numIndices + i
    let x := xs[i]!
    match (← Iargs.findIdxM? fun Iarg => isDefEq Iarg x) with
    | some j => indicesPos := indicesPos.push j
    | none   => throwError "invalid user defined recursor '{declName}', type of the major premise does not contain the recursor index"
  pure indicesPos.toList

private def getMotiveLevel (declName : Name) (motiveResultType : Expr) : MetaM Level :=
  match motiveResultType with
  | Expr.sort u@(Level.zero)    => pure u
  | Expr.sort u@(Level.param _) => pure u
  | _                           =>
    throwError "invalid user defined recursor '{declName}', motive result sort must be Prop or (Sort u) where u is a universe level parameter"

private def getUnivLevelPos (declName : Name) (lparams : List Name) (motiveLvl : Level) (Ilevels : List Level) : MetaM (List RecursorUnivLevelPos) := do
  let Ilevels := Ilevels.toArray
  let mut univLevelPos := #[]
  for p in lparams do
    if motiveLvl == mkLevelParam p then
      univLevelPos := univLevelPos.push RecursorUnivLevelPos.motive
    else
      match Ilevels.findIdx? fun u => u == mkLevelParam p with
      | some i => univLevelPos := univLevelPos.push (RecursorUnivLevelPos.majorType i)
      | none   =>
        throwError "invalid user defined recursor '{declName}', major premise type does not contain universe level parameter '{p}'"
  pure univLevelPos.toList

private def getProduceMotiveAndRecursive (xs : Array Expr) (numParams numIndices majorPos : Nat) (motive : Expr) : MetaM (List Bool × Bool) := do
  let mut produceMotive := #[]
  let mut recursor      := false
  for h : i in [:xs.size] do
    if i < numParams + 1 then
      continue --skip parameters and motive
    if majorPos - numIndices ≤ i && i ≤ majorPos then
      continue -- skip indices and major premise
    -- process minor premise
    let x := xs[i]
    let xType ← inferType x
    (produceMotive, recursor) ← forallTelescopeReducing xType fun minorArgs minorResultType => minorResultType.withApp fun res _ => do
      let produceMotive := produceMotive.push (res == motive)
      let recursor ← if recursor then pure recursor else minorArgs.anyM fun minorArg => do
        let minorArgType ← inferType minorArg
        pure (minorArgType.find? fun e => e == motive).isSome
      pure (produceMotive, recursor)
  pure (produceMotive.toList, recursor)

private def checkMotiveResultType (declName : Name) (motiveArgs : Array Expr) (motiveResultType : Expr) (motiveTypeParams : Array Expr) : MetaM Unit := do
  if !motiveResultType.isSort || motiveArgs.size != motiveTypeParams.size then
    throwError "invalid user defined recursor '{declName}', motive must have a type of the form (C : Pi (i : B A), I A i -> Type), where A is (possibly empty) sequence of variables (aka parameters), (i : B A) is a (possibly empty) telescope (aka indices), and I is a constant"

private def mkRecursorInfoCore (declName : Name) (majorPos? : Option Nat) : MetaM RecursorInfo := do
  let cinfo ← getConstInfo declName
  let majorPos? ← getMajorPosIfAuxRecursor? declName majorPos?
  forallTelescopeReducing cinfo.type fun xs type => type.withApp fun motive motiveArgs => do
    checkMotive declName motive motiveArgs
    let numParams := getNumParams xs motive 0
    let (major, majorPos, depElim) ← getMajorPosDepElim declName majorPos? xs motiveArgs
    let numIndices := if depElim then motiveArgs.size - 1 else motiveArgs.size
    if majorPos < numIndices then
      throwError "invalid user defined recursor '{declName}', indices must occur before major premise"
    let majorType ← inferType major
    majorType.withApp fun I Iargs =>
    match I with
    | Expr.const Iname Ilevels => do
      let paramsPos ← getParamsPos declName xs numParams Iargs
      let indicesPos ← getIndicesPos declName xs majorPos numIndices Iargs
      let motiveType ← inferType motive
      forallTelescopeReducing motiveType fun motiveTypeParams motiveResultType => do
        checkMotiveResultType declName motiveArgs motiveResultType motiveTypeParams
        let motiveLvl ← getMotiveLevel declName motiveResultType
        let univLevelPos ← getUnivLevelPos declName cinfo.levelParams motiveLvl Ilevels
        let (produceMotive, recursive) ← getProduceMotiveAndRecursive xs numParams numIndices majorPos motive
        pure {
          recursorName  := declName,
          typeName      := Iname,
          univLevelPos  := univLevelPos,
          majorPos      := majorPos,
          depElim       := depElim,
          recursive     := recursive,
          produceMotive := produceMotive,
          paramsPos     := paramsPos,
          indicesPos    := indicesPos,
          numArgs       := xs.size
        }
    | _ => throwError "invalid user defined recursor '{declName}', type of the major premise must be of the form (I ...), where I is a constant"

/-
@[builtin_attr_parser] def «recursor» := leading_parser "recursor " >> numLit
-/
def Attribute.Recursor.getMajorPos (stx : Syntax) : AttrM Nat := do
  if stx.getKind == `Lean.Parser.Attr.recursor then
    let pos := stx[1].isNatLit?.getD 0
    if pos == 0 then
      throwErrorAt stx "major premise position must be greater than zero"
    return pos - 1
  else
    throwErrorAt stx "unexpected attribute argument, numeral expected"

builtin_initialize recursorAttribute : ParametricAttribute Nat ←
  registerParametricAttribute {
    name := `recursor,
    descr := "user defined recursor, numerical parameter specifies position of the major premise",
    getParam := fun _ stx => Attribute.Recursor.getMajorPos stx
    afterSet := fun declName majorPos => do
      discard <| mkRecursorInfoCore declName (some majorPos) |>.run'
  }

def getMajorPos? (env : Environment) (declName : Name) : Option Nat :=
  recursorAttribute.getParam? env declName

def mkRecursorInfo (declName : Name) (majorPos? : Option Nat := none) : MetaM RecursorInfo := do
  let majorPos? := majorPos? <|> getMajorPos? (← getEnv) declName
  mkRecursorInfoCore declName majorPos?

end Lean.Meta

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Control
import Init.Lean.AuxRecursor
import Init.Lean.Meta.ExprDefEq

namespace Lean
namespace Meta

inductive RecursorUnivLevelPos
| motive                -- marks where the universe of the motive should go
| majorType (idx : Nat) -- marks where the #idx universe of the major premise type goes

instance RecursorUnivLevelPos.hasToString : HasToString RecursorUnivLevelPos :=
⟨fun pos => match pos with
  | RecursorUnivLevelPos.motive        => "<motive-univ>"
  | RecursorUnivLevelPos.majorType idx => toString idx⟩

structure RecursorInfo :=
(recursorName  : Name)
(typeName      : Name)
(univLevelPos  : List RecursorUnivLevelPos)
(depElim       : Bool)
(recursive     : Bool)
(numArgs       : Nat) -- Total number of arguments
(majorPos      : Nat)
(paramsPos     : List (Option Nat)) -- Position of the recursor parameters in the major premise
(indicesPos    : List Nat) -- Position of the recursor indices in the major premise
(produceMotive : List Bool) -- If the i-th element is true then i-th minor premise produces the motive

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
let r := info.numArgs;
let r := r - info.motivePos - 1;
r - (info.majorPos + 1 - info.firstIndexPos)

instance : HasToString RecursorInfo :=
⟨fun info =>
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
  "}"⟩

end RecursorInfo

private def getMajorPosIfAuxRecursor? (declName : Name) (majorPos? : Option Nat) : MetaM (Option Nat) :=
if majorPos?.isSome then pure majorPos?
else do
  env ← getEnv;
  if !isAuxRecursor env declName then pure none
  else match declName with
  | Name.str p s _ =>
    if s != "recOn" && s != "casesOn" && s != "brecOn" then
      pure none
    else do
      recInfo ← getConstInfo (mkNameStr p "rec");
      match recInfo with
      | ConstantInfo.recInfo val => pure (some (val.nparams + val.nindices + (if s == "casesOn" then 1 else val.nmotives)))
      | _                        => throw $ Exception.other "unexpected recursor information"
  | _ => pure none

private def checkMotive (declName : Name) (motive : Expr) (motiveArgs : Array Expr) : MetaM Unit :=
unless (motive.isFVar && motiveArgs.all Expr.isFVar) $ throw $ Exception.other
  ("invalid user defined recursor '" ++ toString declName ++ "', result type must be of the form (C t), " ++
   "where C is a bound variable, and t is a (possibly empty) sequence of bound variables")

/- Compute number of parameters for (user-defined) recursor.
   We assume a parameter is anything that occurs before the motive -/
private partial def getNumParams (xs : Array Expr) (motive : Expr) : Nat → Nat
| i =>
  if h : i < xs.size then
    let x := xs.get ⟨i, h⟩;
    if motive == x then i
    else getNumParams (i+1)
  else
    i

private def getMajorPosDepElim (declName : Name) (majorPos? : Option Nat) (xs : Array Expr) (motive : Expr) (motiveArgs : Array Expr)
    : MetaM (Expr × Nat × Bool) := do
match majorPos? with
| some majorPos =>
  if h : majorPos < xs.size then
    let major   := xs.get ⟨majorPos, h⟩;
    let depElim := motiveArgs.contains major;
    pure (major, majorPos, depElim)
  else throw $ Exception.other
    ("invalid major premise position for user defined recursor, recursor has only " ++ toString xs.size ++ " arguments")
| none => do
  when motiveArgs.isEmpty $ throw $ Exception.other
    ("invalid user defined recursor, '" ++ toString declName ++ "' does not support dependent elimination, " ++
     "and position of the major premise was not specified " ++
     "(solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)");
  let major := motiveArgs.back;
  match xs.getIdx? major with
  | some majorPos => pure (major, majorPos, true)
  | none          => throw $ Exception.other ("ill-formed recursor '" ++ toString declName ++ "'")

private def getParamsPos (declName : Name) (xs : Array Expr) (numParams : Nat) (Iargs : Array Expr) : MetaM (List (Option Nat)) := do
paramsPos ← numParams.foldM
  (fun i (paramsPos : Array (Option Nat)) => do
    let x := xs.get! i;
    j? ← Iargs.findIdxM? $ fun Iarg => isDefEq Iarg x;
    match j? with
    | some j => pure $ paramsPos.push (some j)
    | none   => do
      localDecl ← getLocalDecl x.fvarId!;
      if localDecl.binderInfo.isInstImplicit then
        pure $ paramsPos.push none
      else
        throw $ Exception.other
          ("invalid user defined recursor '" ++ toString declName ++ "' , type of the major premise does not contain the recursor parameter"))
  #[];
pure paramsPos.toList

private def getIndicesPos (declName : Name) (xs : Array Expr) (majorPos numIndices : Nat) (Iargs : Array Expr) : MetaM (List Nat) := do
indicesPos ← numIndices.foldM
  (fun i (indicesPos : Array Nat) => do
    let i := majorPos - numIndices + i;
    let x := xs.get! i;
    trace! `Meta ("getIndicesPos " ++ toString i ++ ": " ++ x);
    j? ← Iargs.findIdxM? $ fun Iarg => isDefEq Iarg x;
    match j? with
    | some j => pure $ indicesPos.push j
    | none   => throw $ Exception.other
      ("invalid user defined recursor '" ++ toString declName ++ "' , type of the major premise does not contain the recursor index"))
  #[];
pure indicesPos.toList

def mkRecursorInfo (declName : Name) (majorPos? : Option Nat := none) : MetaM RecursorInfo := do
cinfo ← getConstInfo declName;
match cinfo with
| ConstantInfo.recInfo val => do
  indInfo ← getConstInfo val.getInduct;
  match indInfo with
  | ConstantInfo.inductInfo ival =>
    let numLParams    := ival.lparams.length;
    let univLevelPos  := (List.range numLParams).map RecursorUnivLevelPos.majorType;
    let univLevelPos  := if val.lparams.length == numLParams then univLevelPos else RecursorUnivLevelPos.motive :: univLevelPos;
    let produceMotive := List.replicate val.nminors true;
    let paramsPos     := (List.range val.nparams).map some;
    let indicesPos    := (List.range val.nindices).map (fun pos => val.nparams + pos);
    let numArgs       := val.nindices + val.nparams + val.nminors + val.nmotives + 1;
    pure {
     recursorName  := declName,
     typeName      := val.getInduct,
     univLevelPos  := univLevelPos,
     majorPos      := val.getMajorIdx,
     depElim       := true,
     recursive     := ival.isRec,
     produceMotive := produceMotive,
     paramsPos     := paramsPos,
     indicesPos    := indicesPos,
     numArgs       := numArgs
    }
  | _ => throw $ Exception.other "ill-formed builtin recursor"
| _ => do
  majorPos? ← getMajorPosIfAuxRecursor? declName majorPos?;
  forallTelescopeReducing cinfo.type $ fun xs type => type.withApp $ fun motive motiveArgs => do
    checkMotive declName motive motiveArgs;
    let numParams := getNumParams xs motive 0;
    (major, majorPos, depElim) ← getMajorPosDepElim declName majorPos? xs motive motiveArgs;
    let numIndices := if depElim then motiveArgs.size - 1 else motiveArgs.size;
    when (majorPos < numIndices) $ throw $ Exception.other
      ("invalid user defined recursor '" ++ toString declName ++ "', indices must occur before major premise");
    trace! `Meta ("majorPos: " ++ toString majorPos ++ ", depElim: " ++ toString depElim ++ ", numIndices: " ++ toString numIndices);
    majorType ← inferType major;
    majorType.withApp $ fun I Iargs =>
      match I with
      | Expr.const Iname Ilevels _ => do
        trace! `Meta ("Iargs: " ++ Iargs);
        paramsPos ← getParamsPos declName xs numParams Iargs;
        indicesPos ← getIndicesPos declName xs majorPos numIndices Iargs;
        trace! `Meta ("paramsPos: " ++ toString paramsPos ++ ", indicesPos: " ++ toString indicesPos);
        motiveType ← inferType motive;
        forallTelescopeReducing motiveType $ fun motiveTypeParams motiveResultType => do
          when (!motiveResultType.isSort || motiveArgs.size != motiveTypeParams.size) $ throw $ Exception.other
            ("invalid user defined recursor '" ++ toString declName ++ "', motive must have a type of the form "
             ++ "(C : Pi (i : B A), I A i -> Type), where A is (possibly empty) sequence of variables (aka parameters), "
             ++ "(i : B A) is a (possibly empty) telescope (aka indices), and I is a constant");
          -- TODO
          throw $ arbitrary _
      | _ => throw $ Exception.other
        ("invalid user defined recursor '" ++ toString declName
         ++ "', type of the major premise must be of the form (I ...), where I is a constant")

end Meta
end Lean

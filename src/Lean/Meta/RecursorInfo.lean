/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.AuxRecursor
import Lean.Util.FindExpr
import Lean.Meta.ExprDefEq
import Lean.Meta.Message

namespace Lean
namespace Meta

def casesOnSuffix := "casesOn"
def recOnSuffix   := "recOn"
def brecOnSuffix  := "brecOn"

def mkCasesOnFor (indDeclName : Name) : Name := mkNameStr indDeclName casesOnSuffix
def mkRecOnFor (indDeclName : Name) : Name   := mkNameStr indDeclName recOnSuffix
def mkBRecOnFor (indDeclName : Name) : Name  := mkNameStr indDeclName brecOnSuffix

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
(paramsPos     : List (Option Nat)) -- Position of the recursor parameters in the major premise, instance implicit arguments are `none`
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
  "  produceMotive  := " ++ toString info.produceMotive ++ "\n" ++
  "}"⟩

end RecursorInfo

private def mkRecursorInfoForKernelRec (declName : Name) (val : RecursorVal) : MetaM RecursorInfo := do
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
| _ => throwError "ill-formed builtin recursor"

private def getMajorPosIfAuxRecursor? (declName : Name) (majorPos? : Option Nat) : MetaM (Option Nat) :=
if majorPos?.isSome then pure majorPos?
else do
  env ← getEnv;
  if !isAuxRecursor env declName then pure none
  else match declName with
  | Name.str p s _ =>
    if s != recOnSuffix && s != casesOnSuffix && s != brecOnSuffix then
      pure none
    else do
      recInfo ← getConstInfo (mkRecFor p);
      match recInfo with
      | ConstantInfo.recInfo val => pure (some (val.nparams + val.nindices + (if s == casesOnSuffix then 1 else val.nmotives)))
      | _                        => throwError "unexpected recursor information"
  | _ => pure none

private def checkMotive (declName : Name) (motive : Expr) (motiveArgs : Array Expr) : MetaM Unit :=
unless (motive.isFVar && motiveArgs.all Expr.isFVar) $ throwError
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
  else throwError
    ("invalid major premise position for user defined recursor, recursor has only " ++ toString xs.size ++ " arguments")
| none => do
  when motiveArgs.isEmpty $ throwError
    ("invalid user defined recursor, '" ++ toString declName ++ "' does not support dependent elimination, " ++
     "and position of the major premise was not specified " ++
     "(solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)");
  let major := motiveArgs.back;
  match xs.getIdx? major with
  | some majorPos => pure (major, majorPos, true)
  | none          => throwError ("ill-formed recursor '" ++ toString declName ++ "'")

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
        throwError
          ("invalid user defined recursor '" ++ toString declName ++ "' , type of the major premise does not contain the recursor parameter"))
  #[];
pure paramsPos.toList

private def getIndicesPos (declName : Name) (xs : Array Expr) (majorPos numIndices : Nat) (Iargs : Array Expr) : MetaM (List Nat) := do
indicesPos ← numIndices.foldM
  (fun i (indicesPos : Array Nat) => do
    let i := majorPos - numIndices + i;
    let x := xs.get! i;
    -- trace! `Meta ("getIndicesPos " ++ toString i ++ ": " ++ x);
    j? ← Iargs.findIdxM? $ fun Iarg => isDefEq Iarg x;
    match j? with
    | some j => pure $ indicesPos.push j
    | none   => throwError
      ("invalid user defined recursor '" ++ toString declName ++ "' , type of the major premise does not contain the recursor index"))
  #[];
pure indicesPos.toList

private def getMotiveLevel (declName : Name) (motiveResultType : Expr) : MetaM Level :=
match motiveResultType with
| Expr.sort u@(Level.zero _) _    => pure u
| Expr.sort u@(Level.param _ _) _ => pure u
| _                               => throwError
 ("invalid user defined recursor '" ++ toString declName ++ "' , motive result sort must be Prop or (Sort u) where u is a universe level parameter")

private def getUnivLevelPos (declName : Name) (lparams : List Name) (motiveLvl : Level) (Ilevels : List Level) : MetaM (List RecursorUnivLevelPos) := do
let Ilevels := Ilevels.toArray;
univLevelPos ← lparams.foldlM
  (fun (univLevelPos : Array RecursorUnivLevelPos) p =>
    if motiveLvl == mkLevelParam p then
      pure $ univLevelPos.push RecursorUnivLevelPos.motive
    else
      match Ilevels.findIdx? $ fun u => u == mkLevelParam p with
      | some i => pure $ univLevelPos.push $ RecursorUnivLevelPos.majorType i
      | none   => throwError
        ("invalid user defined recursor '" ++ toString declName ++ "' , major premise type does not contain universe level parameter '" ++ toString p ++ "'"))
  #[];
pure univLevelPos.toList

private def getProduceMotiveAndRecursive (xs : Array Expr) (numParams numIndices majorPos : Nat) (motive : Expr) : MetaM (List Bool × Bool) := do
(produceMotive, rec) ← xs.size.foldM
  (fun i (p : Array Bool × Bool) =>
    if i < numParams + 1 then pure p -- skip parameters and motive
    else if majorPos - numIndices ≤ i && i ≤ majorPos then pure p -- skip indices and major premise
    else do -- process minor premise
      let (produceMotive, rec) := p;
      let x := xs.get! i;
      xType ← inferType x;
      forallTelescopeReducing xType $ fun minorArgs minorResultType => minorResultType.withApp $ fun res _ => do
        -- trace! `Meta ("xType: " ++ xType ++ ", motive: " ++ motive ++ ", " ++ minorArgs ++ ", " ++ res);
        let produceMotive := produceMotive.push (res == motive);
        rec ← if rec then pure rec else minorArgs.anyM $ fun minorArg => do {
          minorArgType ← inferType minorArg;
          pure $ (minorArgType.find? $ fun e => e == motive).isSome
        };
        pure (produceMotive, rec))
  (#[], false);
pure (produceMotive.toList, rec)

private def checkMotiveResultType (declName : Name) (motiveArgs : Array Expr) (motiveResultType : Expr) (motiveTypeParams : Array Expr) : MetaM Unit :=
when (!motiveResultType.isSort || motiveArgs.size != motiveTypeParams.size) $ throwError
  ("invalid user defined recursor '" ++ toString declName ++ "', motive must have a type of the form "
   ++ "(C : Pi (i : B A), I A i -> Type), where A is (possibly empty) sequence of variables (aka parameters), "
   ++ "(i : B A) is a (possibly empty) telescope (aka indices), and I is a constant")

private def mkRecursorInfoAux (cinfo : ConstantInfo) (majorPos? : Option Nat) : MetaM RecursorInfo := do
let declName := cinfo.name;
majorPos? ← getMajorPosIfAuxRecursor? declName majorPos?;
forallTelescopeReducing cinfo.type $ fun xs type => type.withApp $ fun motive motiveArgs => do
  checkMotive declName motive motiveArgs;
  let numParams := getNumParams xs motive 0;
  (major, majorPos, depElim) ← getMajorPosDepElim declName majorPos? xs motive motiveArgs;
  let numIndices := if depElim then motiveArgs.size - 1 else motiveArgs.size;
  when (majorPos < numIndices) $ throwError
    ("invalid user defined recursor '" ++ toString declName ++ "', indices must occur before major premise");
  majorType ← inferType major;
  majorType.withApp $ fun I Iargs =>
  match I with
  | Expr.const Iname Ilevels _ => do
    paramsPos ← getParamsPos declName xs numParams Iargs;
    indicesPos ← getIndicesPos declName xs majorPos numIndices Iargs;
    motiveType ← inferType motive;
    forallTelescopeReducing motiveType $ fun motiveTypeParams motiveResultType => do
      checkMotiveResultType declName motiveArgs motiveResultType motiveTypeParams;
      motiveLvl ← getMotiveLevel declName motiveResultType;
      univLevelPos ← getUnivLevelPos declName cinfo.lparams motiveLvl Ilevels;
      (produceMotive, recursive) ← getProduceMotiveAndRecursive xs numParams numIndices majorPos motive;
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
  | _ => throwError
    ("invalid user defined recursor '" ++ toString declName
     ++ "', type of the major premise must be of the form (I ...), where I is a constant")

private def syntaxToMajorPos (stx : Syntax) : Except String Nat :=
match stx with
| Syntax.node _ args =>
  if args.size == 0 then Except.error "unexpected kind of argument"
  else match (args.get! 0).isNatLit? with
    | some idx =>
      if idx == 0 then Except.error "major premise position must be greater than 0"
      else pure (idx - 1)
    | none => Except.error "unexpected kind of argument"
| _ => Except.error "unexpected kind of argument"

private def mkRecursorInfoCore (declName : Name) (majorPos? : Option Nat := none) : MetaM RecursorInfo := do
cinfo ← getConstInfo declName;
match cinfo with
| ConstantInfo.recInfo val => mkRecursorInfoForKernelRec declName val
| _                        => mkRecursorInfoAux cinfo majorPos?

def mkRecursorAttr : IO (ParametricAttribute Nat) :=
registerParametricAttribute `recursor "user defined recursor, numerical parameter specifies position of the major premise"
  (fun _ stx => Core.ofExcept $ syntaxToMajorPos stx)
  (fun declName majorPos => do _ ← (mkRecursorInfoCore declName (some majorPos)).run; pure ())

@[init mkRecursorAttr] constant recursorAttribute : ParametricAttribute Nat := arbitrary _

def getMajorPos? (env : Environment) (declName : Name) : Option Nat :=
recursorAttribute.getParam env declName

def mkRecursorInfo (declName : Name) (majorPos? : Option Nat := none) : MetaM RecursorInfo := do
cinfo ← getConstInfo declName;
match cinfo with
| ConstantInfo.recInfo val => mkRecursorInfoForKernelRec declName val
| _                        => match majorPos? with
  | none => do env ← getEnv; mkRecursorInfoAux cinfo (getMajorPos? env declName)
  | _    => mkRecursorInfoAux cinfo majorPos?

end Meta
end Lean

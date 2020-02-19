/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic

namespace Lean
namespace Meta

inductive RecursorUnivLevelPos
| motive                -- marks where the universe of the motive should go
| majorType (idx : Nat) -- marks where the #idx universe of the major premise type goes

instance RecursorUnivLevelPos.hasToString : HasToString RecursorUnivLevelPos :=
⟨fun pos => match pos with
  | RecursorUnivLevelPos.motive        => "[motive univ]"
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
  "{ name           := " ++ toString info.recursorName ++ "\n" ++
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

def mkRecursorInfo (declName : Name) (majorPos? : Option Nat := none) : MetaM RecursorInfo := do
cinfo ← getConstInfo declName;
match cinfo with
| ConstantInfo.recInfo val => do
  recInfo ← getConstInfo val.getInduct;
  match recInfo with
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
| _ =>
  -- TODO
  throw $ arbitrary _

end Meta
end Lean

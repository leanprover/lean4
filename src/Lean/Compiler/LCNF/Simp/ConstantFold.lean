/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.UInt.Log2
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF.Simp
namespace ConstantFold

/--
A constant folding monad, the additional state stores auxiliary declarations
required to build the new constant.
-/
abbrev FolderM := StateRefT (Array CodeDecl) CompilerM

/--
A constant folder for a specific function, takes all the arguments of a
certain function and produces a new `Expr` + auxiliary declarations in
the `FolderM` monad on success. If the folding fails it returns `none`.
-/
abbrev Folder := Array Arg → FolderM (Option LetValue)

/--
A typeclass for detecting and producing literals of arbitrary types
inside of LCNF.
-/
class Literal (α : Type) where
  /--
  Attempt to turn the provided `Expr` into a value of type `α` if
  it is whatever concept of a literal `α` has. Note that this function
  does assume that the provided `Expr` does indeed have type `α`.
  -/
  getLit : FVarId → CompilerM (Option α)
  /--
  Turn a value of type `α` into a series of auxiliary `LetDecl`s + a
  final `Expr` putting them all together into a literal of type `α`,
  where again the idea of what a literal is depends on `α`.
  -/
  mkLit : α → FolderM LetValue

export Literal (getLit mkLit)

/--
A wrapper around `LCNF.mkAuxLetDecl` that will automatically store the
`LetDecl` in the state of `FolderM`.
-/
def mkAuxLetDecl (e : LetValue) (prefixName := `_x) : FolderM FVarId := do
  let decl ← LCNF.mkAuxLetDecl e prefixName
  modify fun s => s.push <| .let decl
  return decl.fvarId

section Literals

/--
A wrapper around `mkAuxLetDecl` that also calls `mkLit`.
-/
def mkAuxLit [Literal α] (x : α) (prefixName := `_x) : FolderM FVarId := do
  let lit ← mkLit x
  mkAuxLetDecl lit prefixName

partial def getNatLit (fvarId : FVarId) : CompilerM (Option Nat) := do
  let some (.lit (.nat n)) ← findLetValue? fvarId | return none
  return n

def mkNatLit (n : Nat) : FolderM LetValue :=
  return .lit (.nat n)

instance : Literal Nat where
  getLit := getNatLit
  mkLit := mkNatLit

def getStringLit (fvarId : FVarId) : CompilerM (Option String) := do
  let some (.lit (.str s)) ← findLetValue? fvarId | return none
  return s

def mkStringLit (n : String) : FolderM LetValue :=
  return .lit (.str n)

instance : Literal String where
  getLit := getStringLit
  mkLit := mkStringLit

def getBoolLit (fvarId : FVarId) : CompilerM (Option Bool) := do
  let some (.const ctor [] #[]) ← findLetValue? fvarId | return none
  return ctor == ``Bool.true

def mkBoolLit (b : Bool) : FolderM LetValue :=
  let ctor := if b then ``Bool.true else ``Bool.false
  return .const ctor [] #[]

instance : Literal Bool where
  getLit := getBoolLit
  mkLit := mkBoolLit

private partial def getLitAux [Inhabited α] (fvarId : FVarId) (ofNat : Nat → α) (ofNatName : Name) : CompilerM (Option α) := do
  let some (.const declName _ #[.fvar fvarId]) ← findLetValue? fvarId | return none
  unless declName == ofNatName do return none
  let some natLit ← getLit fvarId | return none
  return ofNat natLit

def mkNatWrapperInstance [Inhabited α] (ofNat : Nat → α) (ofNatName : Name) (toNat : α → Nat) : Literal α where
  getLit := (getLitAux · ofNat ofNatName)
  mkLit x := do
    let helperId ← mkAuxLit <| toNat x
    return .const ofNatName [] #[.fvar helperId]

instance : Literal UInt8 := mkNatWrapperInstance UInt8.ofNat ``UInt8.ofNat UInt8.toNat
instance : Literal UInt16 := mkNatWrapperInstance UInt16.ofNat ``UInt16.ofNat UInt16.toNat
instance : Literal UInt32 := mkNatWrapperInstance UInt32.ofNat ``UInt32.ofNat UInt32.toNat
instance : Literal UInt64 := mkNatWrapperInstance UInt64.ofNat ``UInt64.ofNat UInt64.toNat
instance : Literal Char := mkNatWrapperInstance Char.ofNat ``Char.ofNat Char.toNat

end Literals

/--
Turns an expression chain of the form
```
let _x.1 := @List.nil _
let _x.2 := @List.cons _ a _x.1
let _x.3 := @List.cons _ b _x.2
let _x.4 := @List.cons _ c _x.3
let _x.5 := @List.cons _ d _x.4
let _x.6 := @List.cons _ e _x.5
```
into: `[a, b, c, d ,e]` + The type contained in the list
-/
partial def getPseudoListLiteral (fvarId : FVarId) : CompilerM (Option (List FVarId × Expr × Level)) := do
  go fvarId []
where
  go (fvarId : FVarId) (fvarIds : List FVarId) : CompilerM (Option (List FVarId × Expr × Level)) := do
    let some e ← findLetValue? fvarId | return none
    match e with
    | .const ``List.nil [u] #[.type α] =>
      return some (fvarIds.reverse, α, u)
    | .const ``List.cons _ #[_, .fvar h, .fvar t] =>
      go t (h :: fvarIds)
    | _ => return none

/--
Turn an `#[a, b, c]` into:
```
let _x.12 := 3
let _x.8 := @Array.mkEmpty _ _x.12
let _x.22 := @Array.push _ _x.8 x
let _x.24 := @Array.push _ _x.22 y
let _x.26 := @Array.push _ _x.24 z
_x.26
```
-/
def mkPseudoArrayLiteral (elements : Array FVarId) (typ : Expr) (typLevel : Level) : FolderM LetValue := do
  let sizeLit ← mkAuxLit elements.size
  let mut literal ← mkAuxLetDecl <| .const ``Array.mkEmpty [typLevel] #[.type typ, .fvar sizeLit]
  for element in elements do
    literal ← mkAuxLetDecl <| .const ``Array.push [typLevel] #[.type typ, .fvar literal, .fvar element]
  return .fvar literal #[]

/--
Evaluate array literals at compile time, that is turn:
```
let _x.1 := @List.nil _
let _x.2 := @List.cons _ z _x.1
let _x.3 := @List.cons _ y _x.2
let _x.4 := @List.cons _ x _x.3
let _x.5 := @List.toArray _ _x.4
```
To its array form:
```
let _x.12 := 3
let _x.8 := @Array.mkEmpty _ _x.12
let _x.22 := @Array.push _ _x.8 x
let _x.24 := @Array.push _ _x.22 y
let _x.26 := @Array.push _ _x.24 z
```
-/
def foldArrayLiteral : Folder := fun args => do
  let #[_, .fvar fvarId] := args | return none
  let some (list, typ, level) ← getPseudoListLiteral fvarId | return none
  let arr := Array.mk list
  let lit ← mkPseudoArrayLiteral arr typ level
  return some lit

/--
Turn a unary function such as `Nat.succ` into a constant folder.
-/
def Folder.mkUnary [Literal α] [Literal β] (folder : α → β) : Folder := fun args => do
  let #[.fvar fvarId] := args | return none
  let some arg1 ← getLit fvarId | return none
  let res := folder arg1
  mkLit res

/--
Turn a binary function such as `Nat.add` into a constant folder.
-/
def Folder.mkBinary [Literal α] [Literal β] [Literal γ] (folder : α → β → γ) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getLit fvarId₁ | return none
  let some arg₂ ← getLit fvarId₂ | return none
  mkLit <| folder arg₁ arg₂

def Folder.mkBinaryDecisionProcedure [Literal α] [Literal β] {r : α → β → Prop} (folder : (a : α) → (b : β) → Decidable (r a b)) : Folder := fun args => do
  if (← getPhase) < .mono then
    return none
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getLit fvarId₁ | return none
  let some arg₂ ← getLit fvarId₂ | return none
  let boolLit := folder arg₁ arg₂ |>.decide
  mkLit boolLit

/--
Provide a folder for an operation with a left neutral element.
-/
def Folder.leftNeutral [Literal α] [BEq α] (neutral : α) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getLit fvarId₁ | return none
  unless arg₁ == neutral do return none
  return some <| .fvar fvarId₂ #[]

/--
Provide a folder for an operation with a right neutral element.
-/
def Folder.rightNeutral [Literal α] [BEq α] (neutral : α) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₂ ← getLit fvarId₂ | return none
  unless arg₂ == neutral do return none
  return some <| .fvar fvarId₁ #[]

/--
Provide a folder for an operation with a left annihilator.
-/
def Folder.leftAnnihilator [Literal α] [BEq α] (annihilator : α) (zero : α) : Folder := fun args => do
  let #[.fvar fvarId, _] := args | return none
  let some arg ← getLit fvarId | return none
  unless arg == annihilator do return none
  mkLit zero

/--
Provide a folder for an operation with a right annihilator.
-/
def Folder.rightAnnihilator [Literal α] [BEq α] (annihilator : α) (zero : α) : Folder := fun args => do
  let #[_, .fvar fvarId] := args | return none
  let some arg ← getLit fvarId | return none
  unless arg == annihilator do return none
  mkLit zero

def Folder.divShift [Literal α] [BEq α] (shiftRight : Name) (pow2 : α → α) (log2 : α → α) : Folder := fun args => do
  unless (← getEnv).contains shiftRight do return none
  let #[lhs, .fvar fvarId] := args | return none
  let some rhs ← getLit fvarId | return none
  let exponent := log2 rhs
  unless pow2 exponent == rhs do return none
  let shiftLit ← mkAuxLit exponent
  return some <| .const shiftRight [] #[lhs, .fvar shiftLit]

def Folder.mulRhsShift [Literal α] [BEq α] (shiftLeft : Name) (pow2 : α → α) (log2 : α → α) : Folder := fun args => do
  unless (← getEnv).contains shiftLeft do return none
  let #[lhs, .fvar fvarId] := args | return none
  let some rhs ← getLit fvarId | return none
  let exponent := log2 rhs
  unless pow2 exponent == rhs do return none
  let shiftLit ← mkAuxLit exponent
  return some <| .const shiftLeft [] #[lhs, .fvar shiftLit]

def Folder.mulLhsShift [Literal α] [BEq α] (shiftLeft : Name) (pow2 : α → α) (log2 : α → α) : Folder := fun args => do
  unless (← getEnv).contains shiftLeft do return none
  let #[.fvar fvarId, rhs] := args | return none
  let some lhs ← getLit fvarId | return none
  let exponent := log2 lhs
  unless pow2 exponent == lhs do return none
  let shiftLit ← mkAuxLit exponent
  return some <| .const shiftLeft [] #[rhs, .fvar shiftLit]

/--
Pick the first folder out of `folders` that succeeds.
-/
def Folder.first (folders : Array Folder) : Folder := fun exprs => do
  let backup ← get
  for folder in folders do
    if let some res ← folder exprs then
      return res
    else
      set backup
  return none

/--
Provide a folder for an operation that has the same left and right neutral element.
-/
def Folder.leftRightNeutral [Literal α] [BEq α] (neutral : α) : Folder :=
  Folder.first #[Folder.leftNeutral neutral, Folder.rightNeutral neutral]

/--
Provide a folder for an operation that has the same left and right annihilator.
-/
def Folder.leftRightAnnihilator [Literal α] [BEq α] (annihilator : α) (zero : α) : Folder :=
  Folder.first #[Folder.leftAnnihilator annihilator zero, Folder.rightAnnihilator annihilator zero]

/--
Literal folders for higher order datastructures.
-/
def higherOrderLiteralFolders : List (Name × Folder) := [
  (``List.toArray, foldArrayLiteral)
]

def Folder.mulShift [Literal α] [BEq α] (shiftLeft : Name) (pow2 : α → α) (log2 : α → α) : Folder :=
  Folder.first #[Folder.mulLhsShift shiftLeft pow2 log2, Folder.mulRhsShift shiftLeft pow2 log2]

-- TODO: add option for controlling the limit
def natPowThreshold := 256

def foldNatPow (args : Array Arg) : FolderM (Option LetValue) := do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some value₁ ← getNatLit fvarId₁ | return none
  let some value₂ ← getNatLit fvarId₂ | return none
  if value₂ < natPowThreshold then
    return .some (.lit (.nat (value₁ ^ value₂)))
  else
    return none

/--
Folder for ofNat operations on fixed-sized integer types.
-/
def Folder.ofNat (f : Nat → LitValue) (args : Array Arg) : FolderM (Option LetValue) := do
  let #[.fvar fvarId] := args | return none
  let some value ← getNatLit fvarId | return none
  return some (.lit (f value))

def Folder.toNat (args : Array Arg) : FolderM (Option LetValue) := do
  let #[.fvar fvarId] := args | return none
  let some (.lit lit) ← findLetValue? fvarId | return none
  match lit with
  | .uint8 v | .uint16 v | .uint32 v | .uint64 v | .usize v => return some (.lit (.nat v.toNat))
  | .nat _ | .str _ => return none

/--
All arithmetic folders.
-/
def arithmeticFolders : List (Name × Folder) := [
  (``Nat.succ, Folder.mkUnary Nat.succ),
  (``Nat.add,    Folder.first #[Folder.mkBinary Nat.add, Folder.leftRightNeutral 0]),
  (``UInt8.add,  Folder.first #[Folder.mkBinary UInt8.add, Folder.leftRightNeutral (0 : UInt8)]),
  (``UInt16.add,  Folder.first #[Folder.mkBinary UInt16.add, Folder.leftRightNeutral (0 : UInt16)]),
  (``UInt32.add,  Folder.first #[Folder.mkBinary UInt32.add, Folder.leftRightNeutral (0 : UInt32)]),
  (``UInt64.add,  Folder.first #[Folder.mkBinary UInt64.add, Folder.leftRightNeutral (0 : UInt64)]),
  (``Nat.sub,    Folder.first #[Folder.mkBinary Nat.sub, Folder.leftRightNeutral 0]),
  (``UInt8.sub,  Folder.first #[Folder.mkBinary UInt8.sub, Folder.leftRightNeutral (0 : UInt8)]),
  (``UInt16.sub,  Folder.first #[Folder.mkBinary UInt16.sub, Folder.leftRightNeutral (0 : UInt16)]),
  (``UInt32.sub,  Folder.first #[Folder.mkBinary UInt32.sub, Folder.leftRightNeutral (0 : UInt32)]),
  (``UInt64.sub,  Folder.first #[Folder.mkBinary UInt64.sub, Folder.leftRightNeutral (0 : UInt64)]),
  -- We don't convert Nat multiplication by a power of 2 into a left shift, because the fast path
  -- for multiplication isn't any slower than a fast path for left shift that checks for overflow.
  (``UInt8.mul,  Folder.first #[Folder.mkBinary UInt8.mul, Folder.leftRightNeutral (1 : UInt8), Folder.leftRightAnnihilator (0 : UInt8) 0, Folder.mulShift ``UInt8.shiftLeft (UInt8.shiftLeft 1 ·) UInt8.log2]),
  (``UInt16.mul,  Folder.first #[Folder.mkBinary UInt16.mul, Folder.leftRightNeutral (1 : UInt16), Folder.leftRightAnnihilator (0 : UInt16) 0, Folder.mulShift ``UInt16.shiftLeft (UInt16.shiftLeft 1 ·) UInt16.log2]),
  (``UInt32.mul,  Folder.first #[Folder.mkBinary UInt32.mul, Folder.leftRightNeutral (1 : UInt32), Folder.leftRightAnnihilator (0 : UInt32) 0, Folder.mulShift ``UInt32.shiftLeft (UInt32.shiftLeft 1 ·) UInt32.log2]),
  (``UInt64.mul,  Folder.first #[Folder.mkBinary UInt64.mul, Folder.leftRightNeutral (1 : UInt64), Folder.leftRightAnnihilator (0 : UInt64) 0, Folder.mulShift ``UInt64.shiftLeft (UInt64.shiftLeft 1 ·) UInt64.log2]),
  (``Nat.div,    Folder.first #[Folder.mkBinary Nat.div, Folder.rightNeutral 1, Folder.divShift ``Nat.shiftRight (Nat.pow 2) Nat.log2]),
  (``UInt8.div,  Folder.first #[Folder.mkBinary UInt8.div, Folder.rightNeutral (1 : UInt8), Folder.divShift ``UInt8.shiftRight (UInt8.shiftLeft 1 ·) UInt8.log2]),
  (``UInt16.div,  Folder.first #[Folder.mkBinary UInt16.div, Folder.rightNeutral (1 : UInt16), Folder.divShift ``UInt16.shiftRight (UInt16.shiftLeft 1 ·) UInt16.log2]),
  (``UInt32.div,  Folder.first #[Folder.mkBinary UInt32.div, Folder.rightNeutral (1 : UInt32), Folder.divShift ``UInt32.shiftRight (UInt32.shiftLeft 1 ·) UInt32.log2]),
  (``UInt64.div,  Folder.first #[Folder.mkBinary UInt64.div, Folder.rightNeutral (1 : UInt64), Folder.divShift ``UInt64.shiftRight (UInt64.shiftLeft 1 ·) UInt64.log2]),
  (``Nat.pow, foldNatPow),
  (``Nat.nextPowerOfTwo, Folder.mkUnary Nat.nextPowerOfTwo),
]

def relationFolders : List (Name × Folder) := [
  (``Nat.decEq, Folder.mkBinaryDecisionProcedure Nat.decEq),
  (``Nat.decLt, Folder.mkBinaryDecisionProcedure Nat.decLt),
  (``Nat.decLe, Folder.mkBinaryDecisionProcedure Nat.decLe),
  (``UInt8.decEq, Folder.mkBinaryDecisionProcedure UInt8.decEq),
  (``UInt8.decLt, Folder.mkBinaryDecisionProcedure UInt8.decLt),
  (``UInt8.decLe, Folder.mkBinaryDecisionProcedure UInt8.decLe),
  (``UInt16.decEq, Folder.mkBinaryDecisionProcedure UInt16.decEq),
  (``UInt16.decLt, Folder.mkBinaryDecisionProcedure UInt16.decLt),
  (``UInt16.decLe, Folder.mkBinaryDecisionProcedure UInt16.decLe),
  (``UInt32.decEq, Folder.mkBinaryDecisionProcedure UInt32.decEq),
  (``UInt32.decLt, Folder.mkBinaryDecisionProcedure UInt32.decLt),
  (``UInt32.decLe, Folder.mkBinaryDecisionProcedure UInt32.decLe),
  (``UInt64.decEq, Folder.mkBinaryDecisionProcedure UInt64.decEq),
  (``UInt64.decLt, Folder.mkBinaryDecisionProcedure UInt64.decLt),
  (``UInt64.decLe, Folder.mkBinaryDecisionProcedure UInt64.decLe),
  (``Bool.decEq, Folder.mkBinaryDecisionProcedure Bool.decEq),
  (``Bool.decEq, Folder.mkBinaryDecisionProcedure String.decEq)
]

def conversionFolders : List (Name × Folder) := [
  (``UInt8.ofNat, Folder.ofNat (fun v => .uint8 (UInt8.ofNat v))),
  (``UInt16.ofNat, Folder.ofNat (fun v => .uint16 (UInt16.ofNat v))),
  (``UInt32.ofNat, Folder.ofNat (fun v => .uint32 (UInt32.ofNat v))),
  (``UInt64.ofNat, Folder.ofNat (fun v => .uint64 (UInt64.ofNat v))),
  (``USize.ofNat, Folder.ofNat (fun v => .usize (UInt64.ofNat v))),
  (``Char.ofNat, Folder.ofNat (fun v => .uint32 (Char.ofNat v).val)),
  (``UInt8.toNat, Folder.toNat),
  (``UInt16.toNat, Folder.toNat),
  (``UInt32.toNat, Folder.toNat),
  (``UInt64.toNat, Folder.toNat),
  (``USize.toNat, Folder.toNat),
]

/--
All string folders.
-/
def stringFolders : List (Name × Folder) := [
  (``String.append, Folder.first #[Folder.mkBinary String.append, Folder.leftRightNeutral ""]),
  (``String.length, Folder.mkUnary String.length),
  (``String.push, Folder.mkBinary String.push)
]

/--
Apply all known folders to `decl`.
-/
def applyFolders (decl : LetDecl) (folders : SMap Name Folder) : CompilerM (Option (Array CodeDecl)) := do
  match decl.value with
  | .const name _ args =>
    if let some folder := folders.find? name then
      if let (some res, aux) ← folder args |>.run #[] then
        let decl ← decl.updateValue res
        return some <| aux.push (.let decl)
    return none
  | _ => return none

private unsafe def getFolderCoreUnsafe (env : Environment) (opts : Options) (declName : Name) : ExceptT String Id Folder :=
  env.evalConstCheck Folder opts ``Folder declName

@[implemented_by getFolderCoreUnsafe]
private opaque getFolderCore (env : Environment) (opts : Options) (declName : Name) : ExceptT String Id Folder

private def getFolder (declName : Name) : CoreM Folder := do
  ofExcept <| getFolderCore (← getEnv) (← getOptions) declName

def builtinFolders : SMap Name Folder :=
  (arithmeticFolders ++ relationFolders ++ conversionFolders ++ higherOrderLiteralFolders ++ stringFolders).foldl (init := {}) fun s (declName, folder) =>
    s.insert declName folder

structure FolderOleanEntry where
  declName : Name
  folderDeclName : Name

structure FolderEntry extends FolderOleanEntry where
  folder : Folder

builtin_initialize folderExt : PersistentEnvExtension FolderOleanEntry FolderEntry (List FolderEntry × SMap Name Folder) ←
  registerPersistentEnvExtension {
    mkInitial := return ([], builtinFolders)
    addImportedFn := fun entriesArray => do
      let ctx ← read
      let mut folders := builtinFolders
      for entries in entriesArray do
        for { declName, folderDeclName } in entries do
          let folder ← IO.ofExcept <| getFolderCore ctx.env ctx.opts folderDeclName
          folders := folders.insert declName folder
      return ([], folders.switch)
    addEntryFn := fun (entries, map) entry => (entry :: entries, map.insert entry.declName entry.folder)
    exportEntriesFn := fun (entries, _) => entries.reverse.toArray.map (·.toFolderOleanEntry)
    asyncMode := .sync
    replay? := some fun oldState newState _ s =>
      let newEntries := newState.1.take (newState.1.length - oldState.1.length)
      (newEntries ++ s.1, newEntries.foldl (init := s.2) fun s e => s.insert e.declName (newState.2.find! e.declName))
  }

def registerFolder (declName : Name) (folderDeclName : Name) : CoreM Unit := do
  let folder ← getFolder folderDeclName
  modifyEnv fun env => folderExt.addEntry env { declName, folderDeclName, folder }

def getFolders : CoreM (SMap Name Folder) :=
  return folderExt.getState (← getEnv) |>.2

/--
Apply a list of default folders to `decl`
-/
def foldConstants (decl : LetDecl) : CompilerM (Option (Array CodeDecl)) := do
  applyFolders decl (← getFolders)

end ConstantFold
end Lean.Compiler.LCNF.Simp

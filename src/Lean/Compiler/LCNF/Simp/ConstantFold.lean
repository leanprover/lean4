/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.UInt.Log2
public import Lean.Compiler.LCNF.InferType
import Init.Data.UInt.Lemmas

public section

namespace Lean.Compiler.LCNF.Simp
namespace ConstantFold

/--
A constant folding monad, the additional state stores auxiliary declarations
required to build the new constant.
-/
abbrev FolderM := StateRefT (Array (CodeDecl .pure)) CompilerM

/--
A constant folder for a specific function, takes all the arguments of a
certain function and produces a new `Expr` + auxiliary declarations in
the `FolderM` monad on success. If the folding fails it returns `none`.
-/
abbrev Folder := Array (Arg .pure) → FolderM (Option (LetValue .pure))

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
  mkLit : α → FolderM (LetValue .pure)

export Literal (getLit mkLit)

/--
A wrapper around `LCNF.mkAuxLetDecl` that will automatically store the
`LetDecl` in the state of `FolderM`.
-/
def mkAuxLetDecl (e : LetValue .pure) (prefixName := `_x) : FolderM FVarId := do
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

def getNatLit (fvarId : FVarId) : CompilerM (Option Nat) := do
  let some (.lit (.nat n)) ← findLetValue? (pu := .pure) fvarId | return none
  return n

def mkNatLit (n : Nat) : FolderM (LetValue .pure) :=
  return .lit (.nat n)

instance : Literal Nat where
  getLit := getNatLit
  mkLit := mkNatLit

def getStringLit (fvarId : FVarId) : CompilerM (Option String) := do
  let some (.lit (.str s)) ← findLetValue? (pu := .pure) fvarId | return none
  return s

def mkStringLit (n : String) : FolderM (LetValue .pure) :=
  return .lit (.str n)

instance : Literal String where
  getLit := getStringLit
  mkLit := mkStringLit

def getBoolLit (fvarId : FVarId) : CompilerM (Option Bool) := do
  let some (.const name [] #[]) ← findLetValue? fvarId | return none
  match name with
  | ``Bool.true => return some true
  | ``Bool.false => return some false
  | _ => return none

def mkBoolLit (b : Bool) : FolderM (LetValue .pure) :=
  let ctor := if b then ``Bool.true else ``Bool.false
  return .const ctor [] #[]

instance : Literal Bool where
  getLit := getBoolLit
  mkLit := mkBoolLit

def getCharLit (fvarId : FVarId) : CompilerM (Option Char) := do
  /-
  Depending on our phase `Char` is a structure or has been unwrapped to a UInt32, act accordingly.
  -/
  match (← findLetValue? (pu := .pure) fvarId) with
  | some (.lit (.uint32 v)) =>
    unless v.toNat.isValidChar do return none
    return Char.ofNat v.toNat
  | some (.const ``Char.ofNat _ #[.fvar natFVarId]) =>
    let some n ← getNatLit natFVarId | return none
    return Char.ofNat n
  | _ => return none

def mkCharLit (c : Char) : FolderM (LetValue .pure) := do
  /-
  Depending on our phase `Char` is a structure or has been unwrapped to a UInt32, act accordingly.
  -/
  if (← getPhase) < .mono then
    let natId ← mkAuxLit c.toNat
    return .const ``Char.ofNat [] #[.fvar natId]
  else
    return .lit (.uint32 c.val)

instance : Literal Char where
  getLit := getCharLit
  mkLit := mkCharLit

@[instance_reducible]
def mkUIntInstance (matchLit : LitValue → Option α) (litValueCtor : α → LitValue) : Literal α where
  getLit fvarId := do
    let some (.lit litVal) ← findLetValue? (pu := .pure) fvarId | return none
    return matchLit litVal
  mkLit x :=
    return .lit <| litValueCtor x

instance : Literal UInt8 := mkUIntInstance (fun | .uint8 x => some x | _ => none) .uint8
instance : Literal UInt16 := mkUIntInstance (fun | .uint16 x => some x | _ => none) .uint16
instance : Literal UInt32 := mkUIntInstance (fun | .uint32 x => some x | _ => none) .uint32
instance : Literal UInt64 := mkUIntInstance (fun | .uint64 x => some x | _ => none) .uint64

def getUSizeLit (fvarId : FVarId) : CompilerM (Option UInt64) := do
  let some (.lit (.usize n)) ← findLetValue? (pu := .pure) fvarId | return none
  return n

def mkUSizeLit (x : UInt64) : CompilerM (LetValue .pure) := do
  return .lit <| .usize x

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
def mkPseudoArrayLiteral (elements : Array FVarId) (typ : Expr) (typLevel : Level) : FolderM (LetValue .pure) := do
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
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getLit fvarId₁ | return none
  let some arg₂ ← getLit fvarId₂ | return none
  let result := folder arg₁ arg₂ |>.decide
  if (← getPhase) < .mono then
    if result then
      return some <| .const ``Decidable.isTrue [] #[.erased, .erased]
    else
      return some <| .const ``Decidable.isFalse [] #[.erased, .erased]
  else
    mkLit result

/-
We handle `USize` separately as the interpretation of `USize` literals is in general platform dependent
-/
def Folder.mkBinaryUSizeDecisionProcedure {r64 : UInt64 → UInt64 → Prop} {r32 : UInt32 → UInt32 → Prop}
    (f64 : (a b : UInt64) → Decidable (r64 a b)) (f32 : (a b : UInt32) → Decidable (r32 a b)) :
    Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getUSizeLit fvarId₁ | return none
  let some arg₂ ← getUSizeLit fvarId₂ | return none
  let res64 := (f64 arg₁ arg₂).decide
  let res32 := (f32 arg₁.toUInt32 arg₂.toUInt32).decide
  unless res64 == res32 do return none
  if (← getPhase) < .mono then
    if res64 then
      return some <| .const ``Decidable.isTrue [] #[.erased, .erased]
    else
      return some <| .const ``Decidable.isFalse [] #[.erased, .erased]
  else
    mkLit res64

def Folder.mkBinaryUSize (f64 : UInt64 → UInt64 → UInt64) (f32 : UInt32 → UInt32 → UInt32) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getUSizeLit fvarId₁ | return none
  let some arg₂ ← getUSizeLit fvarId₂ | return none
  let res64 := f64 arg₁ arg₂
  let res32 := f32 arg₁.toUInt32 arg₂.toUInt32
  unless res32.toUInt64 == res64 do return none
  mkUSizeLit res64

def Folder.mkUnaryUSize (f64 : UInt64 → UInt64) (f32 : UInt32 → UInt32) : Folder := fun args => do
  let #[.fvar fvarId] := args | return none
  let some arg ← getUSizeLit fvarId | return none
  let res64 := f64 arg
  let res32 := f32 arg.toUInt32
  unless res32.toUInt64 == res64 do return none
  mkUSizeLit res64

def Folder.mkUnaryToUSize [Literal α] (f64 : α → UInt64) (f32 : α → UInt32) : Folder := fun args => do
  let #[.fvar fvarId] := args | return none
  let some arg ← getLit fvarId | return none
  let res64 := f64 arg
  let res32 := f32 arg
  unless res32.toUInt64 == res64 do return none
  mkUSizeLit res64

def Folder.mkUnaryOfUSize [Literal β] [BEq β] (f64 : UInt64 → β) (f32 : UInt32 → β) : Folder := fun args => do
  let #[.fvar fvarId] := args | return none
  let some arg ← getUSizeLit fvarId | return none
  let res64 := f64 arg
  let res32 := f32 arg.toUInt32
  unless res64 == res32 do return none
  mkLit res64

def Folder.leftNeutralUSize (n64 : UInt64) (n32 : UInt32) :
    Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getUSizeLit fvarId₁ | return none
  unless arg₁ == n64 && arg₁.toUInt32 == n32 do return none
  return some <| .fvar fvarId₂ #[]

def Folder.rightNeutralUSize (n64 : UInt64) (n32 : UInt32) :
    Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₂ ← getUSizeLit fvarId₂ | return none
  unless arg₂ == n64 && arg₂.toUInt32 == n32 do return none
  return some <| .fvar fvarId₁ #[]

def Folder.leftAnnihilatorUSize (a64 : UInt64) (a32 : UInt32)
    (zero64 : UInt64) (zero32 : UInt32) : Folder := fun args => do
  let #[.fvar fvarId, _] := args | return none
  let some arg ← getUSizeLit fvarId | return none
  unless arg == a64 && arg.toUInt32 == a32 do return none
  assert! zero64.toUInt32 == zero32
  mkUSizeLit zero64

def Folder.rightAnnihilatorUSize (a64 : UInt64) (a32 : UInt32)
    (zero64 : UInt64) (zero32 : UInt32) : Folder := fun args => do
  let #[_, .fvar fvarId] := args | return none
  let some arg ← getUSizeLit fvarId | return none
  unless arg == a64 && arg.toUInt32 == a32 do return none
  assert! zero64.toUInt32 == zero32
  mkUSizeLit zero64

/--
Provide a folder for an operation with a left neutral element.
-/
def Folder.leftNeutral [Literal α] [BEq α] (neutral : α) (op : α → α → α)
    (_h : ∀ x, op neutral x = x := by simp) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₁ ← getLit fvarId₁ | return none
  unless arg₁ == neutral do return none
  return some <| .fvar fvarId₂ #[]

/--
Provide a folder for an operation with a right neutral element.
-/
def Folder.rightNeutral [Literal α] [BEq α] (neutral : α) (op : α → α → α)
    (_h : ∀ x, op x neutral = x := by simp) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  let some arg₂ ← getLit fvarId₂ | return none
  unless arg₂ == neutral do return none
  return some <| .fvar fvarId₁ #[]

/--
Provide a folder for an operation with a left annihilator.
-/
def Folder.leftAnnihilator [Literal α] [BEq α] [Literal γ] (annihilator : α) (zero : γ)
    (op : α → β → γ) (_h : ∀ x, op annihilator x = zero := by simp) : Folder := fun args => do
  let #[.fvar fvarId, _] := args | return none
  let some arg ← getLit fvarId | return none
  unless arg == annihilator do return none
  mkLit zero

/--
Provide a folder for an operation with a right annihilator. The result type may differ from the
operand types, e.g. `Nat.blt x 0 = false`.
-/
def Folder.rightAnnihilator [Literal β] [BEq β] [Literal γ] (annihilator : β) (zero : γ)
    (op : α → β → γ) (_h : ∀ x, op x annihilator = zero := by simp) : Folder := fun args => do
  let #[_, .fvar fvarId] := args | return none
  let some arg ← getLit fvarId | return none
  unless arg == annihilator do return none
  mkLit zero

def Folder.sameArg [Literal γ] (zero : γ) (op : α → α → γ)
    (_h : ∀ x, op x x = zero := by simp) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  unless fvarId₁ == fvarId₂ do return none
  mkLit zero

def Folder.sameArgUSize (zero64 : UInt64) (zero32 : UInt32) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  unless fvarId₁ == fvarId₂ do return none
  assert! zero64.toUInt32 == zero32
  mkUSizeLit zero64

def Folder.idempotent (op : α → α → α) (_h : ∀ x, op x x = x := by simp) : Folder := fun args => do
  let #[.fvar fvarId₁, .fvar fvarId₂] := args | return none
  unless fvarId₁ == fvarId₂ do return none
  return some <| .fvar fvarId₁ #[]

def Folder.divShift [Literal α] [BEq α] (shiftRight : Name) (pow2 : α → α) (log2 : α → α) : Folder := fun args => do
  unless (← getDecl? shiftRight).isSome do return none
  let #[lhs, .fvar fvarId] := args | return none
  let some rhs ← getLit fvarId | return none
  let exponent := log2 rhs
  unless pow2 exponent == rhs do return none
  let shiftLit ← mkAuxLit exponent
  return some <| .const shiftRight [] #[lhs, .fvar shiftLit]

def Folder.mulRhsShift [Literal α] [BEq α] (shiftLeft : Name) (pow2 : α → α) (log2 : α → α) : Folder := fun args => do
  unless (← getDecl? shiftLeft).isSome do return none
  let #[lhs, .fvar fvarId] := args | return none
  let some rhs ← getLit fvarId | return none
  let exponent := log2 rhs
  unless pow2 exponent == rhs do return none
  let shiftLit ← mkAuxLit exponent
  return some <| .const shiftLeft [] #[lhs, .fvar shiftLit]

def Folder.mulLhsShift [Literal α] [BEq α] (shiftLeft : Name) (pow2 : α → α) (log2 : α → α) : Folder := fun args => do
  unless (← getDecl? shiftLeft).isSome do return none
  let #[.fvar fvarId, rhs] := args | return none
  let some lhs ← getLit fvarId | return none
  let exponent := log2 lhs
  unless pow2 exponent == lhs do return none
  let shiftLit ← mkAuxLit exponent
  return some <| .const shiftLeft [] #[rhs, .fvar shiftLit]

/--
If `x` is a power of two with the same exponent in both its 64 and 32 bit
interpretation, return that exponent.
-/
private def getUSizePow2Exponent? (x : UInt64) : Option UInt64 :=
  let exponent64 := x.log2
  let exponent32 := x.toUInt32.log2
  if UInt64.shiftLeft 1 exponent64 == x && UInt32.shiftLeft 1 exponent32 == x.toUInt32 &&
      exponent64 == exponent32.toUInt64 then
    some exponent64
  else
    none

def Folder.divShiftUSize : Folder := fun args => do
  unless (← getDecl? ``USize.shiftRight).isSome do return none
  let #[lhs, .fvar fvarId] := args | return none
  let some rhs ← getUSizeLit fvarId | return none
  let some exponent := getUSizePow2Exponent? rhs | return none
  let shiftLit ← mkAuxLetDecl (← mkUSizeLit exponent)
  return some <| .const ``USize.shiftRight [] #[lhs, .fvar shiftLit]

def Folder.mulRhsShiftUSize : Folder := fun args => do
  unless (← getDecl? ``USize.shiftLeft).isSome do return none
  let #[lhs, .fvar fvarId] := args | return none
  let some rhs ← getUSizeLit fvarId | return none
  let some exponent := getUSizePow2Exponent? rhs | return none
  let shiftLit ← mkAuxLetDecl (← mkUSizeLit exponent)
  return some <| .const ``USize.shiftLeft [] #[lhs, .fvar shiftLit]

def Folder.mulLhsShiftUSize : Folder := fun args => do
  unless (← getDecl? ``USize.shiftLeft).isSome do return none
  let #[.fvar fvarId, rhs] := args | return none
  let some lhs ← getUSizeLit fvarId | return none
  let some exponent := getUSizePow2Exponent? lhs | return none
  let shiftLit ← mkAuxLetDecl (← mkUSizeLit exponent)
  return some <| .const ``USize.shiftLeft [] #[rhs, .fvar shiftLit]

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
def Folder.leftRightNeutral [Literal α] [BEq α] (neutral : α) (op : α → α → α)
    (_h1 : ∀ x, op neutral x = x := by simp) (_h2 : ∀ x, op x neutral = x := by simp) : Folder :=
  Folder.first #[Folder.leftNeutral neutral op _h1, Folder.rightNeutral neutral op _h2]

/--
Provide a folder for a `USize` operation that has the same left and right neutral element.
-/
def Folder.leftRightNeutralUSize (n64 : UInt64) (n32 : UInt32) : Folder :=
  Folder.first #[Folder.leftNeutralUSize n64 n32, Folder.rightNeutralUSize n64 n32]

/--
Provide a folder for an operation that has the same left and right annihilator.
-/
def Folder.leftRightAnnihilator [Literal α] [BEq α] (annihilator : α) (zero : α)
    (op : α → α → α) (_h1 : ∀ x, op annihilator x = zero := by simp)
    (_h2 : ∀ x, op x annihilator = zero := by simp) : Folder :=
  Folder.first #[
    Folder.leftAnnihilator annihilator zero op _h1,
    Folder.rightAnnihilator annihilator zero op _h2
  ]

/--
Provide a folder for a `USize` operation that has the same left and right annihilator.
-/
def Folder.leftRightAnnihilatorUSize (annihilator64 : UInt64) (annihilator32 : UInt32)
    (zero64 : UInt64) (zero32 : UInt32) : Folder :=
  Folder.first #[
    Folder.leftAnnihilatorUSize annihilator64 annihilator32 zero64 zero32,
    Folder.rightAnnihilatorUSize annihilator64 annihilator32 zero64 zero32
  ]

/--
Literal folders for higher order datastructures.
-/
def higherOrderLiteralFolders : List (Name × Folder) := [
  (``List.toArray, foldArrayLiteral)
]

def Folder.mulShift [Literal α] [BEq α] (shiftLeft : Name) (pow2 : α → α) (log2 : α → α) : Folder :=
  Folder.first #[Folder.mulLhsShift shiftLeft pow2 log2, Folder.mulRhsShift shiftLeft pow2 log2]

def Folder.mulShiftUSize : Folder :=
  Folder.first #[Folder.mulLhsShiftUSize, Folder.mulRhsShiftUSize]

-- TODO: add option for controlling the limit
def natPowThreshold := 256

def foldNatPow (args : Array (Arg .pure)) : FolderM (Option (LetValue .pure)) := do
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
def Folder.ofNat (f : Nat → LitValue) (args : Array (Arg .pure)) : FolderM (Option (LetValue .pure)) := do
  let #[.fvar fvarId] := args | return none
  let some value ← getNatLit fvarId | return none
  return some (.lit (f value))

/--
Folder for `ofNatLT` operations on fixed-sized integer types. The bound is a proof and carries no
runtime content, so only the numeral matters.
-/
def Folder.ofNatLT (f : Nat → LitValue) (args : Array (Arg .pure)) : FolderM (Option (LetValue .pure)) := do
  let #[.fvar fvarId, _] := args | return none
  let some value ← getNatLit fvarId | return none
  return some (.lit (f value))

def Folder.charOfNat (args : Array (Arg .pure)) : FolderM (Option (LetValue .pure)) := do
  if (← getPhase) < .mono then return none
  Folder.ofNat (fun v => .uint32 (Char.ofNat v).val) args

def Folder.toNat (args : Array (Arg .pure)) : FolderM (Option (LetValue .pure)) := do
  let #[.fvar fvarId] := args | return none
  let some (.lit lit) ← findLetValue? (pu := .pure) fvarId | return none
  match lit with
  | .uint8 v | .uint16 v | .uint32 v | .uint64 v => return some (.lit (.nat v.toNat))
  | .usize v => if v.toUInt32.toUInt64 == v then return some (.lit (.nat v.toNat)) else return none
  | .nat _ | .str _ => return none

/--
All arithmetic folders.
-/
def arithmeticFolders : List (Name × Folder) := [
  (``Nat.succ, Folder.mkUnary Nat.succ),
  (``Nat.reprFast, Folder.mkUnary Nat.reprFast),
  (``Nat.add,    Folder.first #[Folder.mkBinary Nat.add, Folder.leftRightNeutral 0 (· + ·)]),
  (``UInt8.add,  Folder.first #[Folder.mkBinary UInt8.add, Folder.leftRightNeutral (0 : UInt8) (· + ·)]),
  (``UInt16.add,  Folder.first #[Folder.mkBinary UInt16.add, Folder.leftRightNeutral (0 : UInt16) (· + ·)]),
  (``UInt32.add,  Folder.first #[Folder.mkBinary UInt32.add, Folder.leftRightNeutral (0 : UInt32) (· + ·)]),
  (``UInt64.add,  Folder.first #[Folder.mkBinary UInt64.add, Folder.leftRightNeutral (0 : UInt64) (· + ·)]),
  (``USize.add,  Folder.first #[Folder.mkBinaryUSize UInt64.add UInt32.add, Folder.leftRightNeutralUSize 0 0]),
  (``Nat.sub,    Folder.first #[Folder.mkBinary Nat.sub, Folder.leftAnnihilator 0 0 (· -  ·), Folder.rightNeutral 0 (· - ·), Folder.sameArg 0 (· - ·) Nat.sub_self]),
  (``UInt8.sub,  Folder.first #[Folder.mkBinary UInt8.sub, Folder.rightNeutral (0 : UInt8) (· - ·), Folder.sameArg (0 : UInt8) (· - ·) UInt8.sub_self]),
  (``UInt16.sub,  Folder.first #[Folder.mkBinary UInt16.sub, Folder.rightNeutral (0 : UInt16) (· - ·), Folder.sameArg (0 : UInt16) (· - ·) UInt16.sub_self]),
  (``UInt32.sub,  Folder.first #[Folder.mkBinary UInt32.sub, Folder.rightNeutral (0 : UInt32) (· - ·), Folder.sameArg (0 : UInt32) (· - ·) UInt32.sub_self]),
  (``UInt64.sub,  Folder.first #[Folder.mkBinary UInt64.sub, Folder.rightNeutral (0 : UInt64) (· - ·), Folder.sameArg (0 : UInt64) (· - ·) UInt64.sub_self]),
  (``USize.sub,  Folder.first #[Folder.mkBinaryUSize UInt64.sub UInt32.sub, Folder.rightNeutralUSize 0 0, Folder.sameArgUSize 0 0]),
  -- We don't convert Nat multiplication by a power of 2 into a left shift, because the fast path
  -- for multiplication isn't any slower than a fast path for left shift that checks for overflow.
  (``Nat.mul, Folder.first #[Folder.mkBinary Nat.mul, Folder.leftRightNeutral (1 : Nat) (· * ·), Folder.leftRightAnnihilator (0 : Nat) 0 (· * ·)]),
  (``UInt8.mul,  Folder.first #[Folder.mkBinary UInt8.mul, Folder.leftRightNeutral (1 : UInt8) (· * ·), Folder.leftRightAnnihilator (0 : UInt8) 0 (· * ·), Folder.mulShift ``UInt8.shiftLeft (UInt8.shiftLeft 1 ·) UInt8.log2]),
  (``UInt16.mul,  Folder.first #[Folder.mkBinary UInt16.mul, Folder.leftRightNeutral (1 : UInt16) (· * ·), Folder.leftRightAnnihilator (0 : UInt16) 0 (· * ·), Folder.mulShift ``UInt16.shiftLeft (UInt16.shiftLeft 1 ·) UInt16.log2]),
  (``UInt32.mul,  Folder.first #[Folder.mkBinary UInt32.mul, Folder.leftRightNeutral (1 : UInt32) (· * ·), Folder.leftRightAnnihilator (0 : UInt32) 0 (· * ·), Folder.mulShift ``UInt32.shiftLeft (UInt32.shiftLeft 1 ·) UInt32.log2]),
  (``UInt64.mul,  Folder.first #[Folder.mkBinary UInt64.mul, Folder.leftRightNeutral (1 : UInt64) (· * ·), Folder.leftRightAnnihilator (0 : UInt64) 0 (· * ·), Folder.mulShift ``UInt64.shiftLeft (UInt64.shiftLeft 1 ·) UInt64.log2]),
  (``USize.mul,  Folder.first #[Folder.mkBinaryUSize UInt64.mul UInt32.mul, Folder.leftRightNeutralUSize 1 1, Folder.leftRightAnnihilatorUSize 0 0 0 0, Folder.mulShiftUSize]),
  (``Nat.div,    Folder.first #[Folder.mkBinary Nat.div, Folder.rightNeutral 1 (· / ·), Folder.leftAnnihilator 0 0 (· / ·) Nat.zero_div, Folder.divShift ``Nat.shiftRight (Nat.pow 2) Nat.log2]),
  (``UInt8.div,  Folder.first #[Folder.mkBinary UInt8.div, Folder.rightNeutral (1 : UInt8) (· / ·), Folder.leftAnnihilator (0 : UInt8) 0 (· / ·) @UInt8.zero_div, Folder.divShift ``UInt8.shiftRight (UInt8.shiftLeft 1 ·) UInt8.log2]),
  (``UInt16.div,  Folder.first #[Folder.mkBinary UInt16.div, Folder.rightNeutral (1 : UInt16) (· / ·), Folder.leftAnnihilator (0 : UInt16) 0 (· / ·) @UInt16.zero_div, Folder.divShift ``UInt16.shiftRight (UInt16.shiftLeft 1 ·) UInt16.log2]),
  (``UInt32.div,  Folder.first #[Folder.mkBinary UInt32.div, Folder.rightNeutral (1 : UInt32) (· / ·), Folder.leftAnnihilator (0 : UInt32) 0 (· / ·) @UInt32.zero_div, Folder.divShift ``UInt32.shiftRight (UInt32.shiftLeft 1 ·) UInt32.log2]),
  (``UInt64.div,  Folder.first #[Folder.mkBinary UInt64.div, Folder.rightNeutral (1 : UInt64) (· / ·), Folder.leftAnnihilator (0 : UInt64) 0 (· / ·) @UInt64.zero_div, Folder.divShift ``UInt64.shiftRight (UInt64.shiftLeft 1 ·) UInt64.log2]),
  (``USize.div,  Folder.first #[Folder.mkBinaryUSize UInt64.div UInt32.div, Folder.rightNeutralUSize 1 1, Folder.leftAnnihilatorUSize 0 0 0 0, Folder.divShiftUSize]),
  (``Nat.mod,    Folder.first #[Folder.mkBinary Nat.mod, Folder.rightNeutral 0 (· % ·) Nat.mod_zero, Folder.leftAnnihilator 0 0 (· % ·) Nat.zero_mod, Folder.rightAnnihilator 1 0 (· % ·) Nat.mod_one, Folder.sameArg 0 (· % ·) Nat.mod_self]),
  (``UInt8.mod,  Folder.first #[Folder.mkBinary UInt8.mod, Folder.rightNeutral (0 : UInt8) (· % ·) @UInt8.mod_zero, Folder.leftAnnihilator (0 : UInt8) 0 (· % ·) @UInt8.zero_mod, Folder.rightAnnihilator (1 : UInt8) 0 (· % ·) @UInt8.mod_one, Folder.sameArg (0 : UInt8) (· % ·) @UInt8.mod_self]),
  (``UInt16.mod,  Folder.first #[Folder.mkBinary UInt16.mod, Folder.rightNeutral (0 : UInt16) (· % ·) @UInt16.mod_zero, Folder.leftAnnihilator (0 : UInt16) 0 (· % ·) @UInt16.zero_mod, Folder.rightAnnihilator (1 : UInt16) 0 (· % ·) @UInt16.mod_one, Folder.sameArg (0 : UInt16) (· % ·) @UInt16.mod_self]),
  (``UInt32.mod,  Folder.first #[Folder.mkBinary UInt32.mod, Folder.rightNeutral (0 : UInt32) (· % ·) @UInt32.mod_zero, Folder.leftAnnihilator (0 : UInt32) 0 (· % ·) @UInt32.zero_mod, Folder.rightAnnihilator (1 : UInt32) 0 (· % ·) @UInt32.mod_one, Folder.sameArg (0 : UInt32) (· % ·) @UInt32.mod_self]),
  (``UInt64.mod,  Folder.first #[Folder.mkBinary UInt64.mod, Folder.rightNeutral (0 : UInt64) (· % ·) @UInt64.mod_zero, Folder.leftAnnihilator (0 : UInt64) 0 (· % ·) @UInt64.zero_mod, Folder.rightAnnihilator (1 : UInt64) 0 (· % ·) @UInt64.mod_one, Folder.sameArg (0 : UInt64) (· % ·) @UInt64.mod_self]),
  (``USize.mod,  Folder.first #[Folder.mkBinaryUSize UInt64.mod UInt32.mod, Folder.rightNeutralUSize 0 0, Folder.leftAnnihilatorUSize 0 0 0 0, Folder.rightAnnihilatorUSize 1 1 0 0, Folder.sameArgUSize 0 0]),

  (``Nat.shiftLeft, Folder.first #[Folder.mkBinary Nat.shiftLeft, Folder.rightNeutral 0 Nat.shiftLeft (by intros; rfl), Folder.leftAnnihilator 0 0 Nat.shiftLeft Nat.zero_shiftLeft]),
  (``UInt8.shiftLeft, Folder.first #[Folder.mkBinary UInt8.shiftLeft, Folder.rightNeutral 0 UInt8.shiftLeft @UInt8.shiftLeft_zero, Folder.leftAnnihilator (0 : UInt8) 0 UInt8.shiftLeft @UInt8.zero_shiftLeft]),
  (``UInt16.shiftLeft, Folder.first #[Folder.mkBinary UInt16.shiftLeft, Folder.rightNeutral 0 UInt16.shiftLeft @UInt16.shiftLeft_zero, Folder.leftAnnihilator (0 : UInt16) 0 UInt16.shiftLeft @UInt16.zero_shiftLeft]),
  (``UInt32.shiftLeft, Folder.first #[Folder.mkBinary UInt32.shiftLeft, Folder.rightNeutral 0 UInt32.shiftLeft @UInt32.shiftLeft_zero, Folder.leftAnnihilator (0 : UInt32) 0 UInt32.shiftLeft @UInt32.zero_shiftLeft]),
  (``UInt64.shiftLeft, Folder.first #[Folder.mkBinary UInt64.shiftLeft, Folder.rightNeutral 0 UInt64.shiftLeft @UInt64.shiftLeft_zero, Folder.leftAnnihilator (0 : UInt64) 0 UInt64.shiftLeft @UInt64.zero_shiftLeft]),
  (``USize.shiftLeft, Folder.first #[Folder.mkBinaryUSize UInt64.shiftLeft UInt32.shiftLeft, Folder.rightNeutralUSize 0 0, Folder.leftAnnihilatorUSize 0 0 0 0]),

  (``Nat.shiftRight, Folder.first #[Folder.mkBinary Nat.shiftRight, Folder.rightNeutral 0 Nat.shiftRight (by intros; rfl), Folder.leftAnnihilator 0 0 Nat.shiftRight Nat.zero_shiftRight]),
  (``UInt8.shiftRight, Folder.first #[Folder.mkBinary UInt8.shiftRight, Folder.rightNeutral 0 UInt8.shiftRight @UInt8.shiftRight_zero, Folder.leftAnnihilator (0 : UInt8) 0 UInt8.shiftRight @UInt8.zero_shiftRight]),
  (``UInt16.shiftRight, Folder.first #[Folder.mkBinary UInt16.shiftRight, Folder.rightNeutral 0 UInt16.shiftRight @UInt16.shiftRight_zero, Folder.leftAnnihilator (0 : UInt16) 0 UInt16.shiftRight @UInt16.zero_shiftRight]),
  (``UInt32.shiftRight, Folder.first #[Folder.mkBinary UInt32.shiftRight, Folder.rightNeutral 0 UInt32.shiftRight @UInt32.shiftRight_zero, Folder.leftAnnihilator (0 : UInt32) 0 UInt32.shiftRight @UInt32.zero_shiftRight]),
  (``UInt64.shiftRight, Folder.first #[Folder.mkBinary UInt64.shiftRight, Folder.rightNeutral 0 UInt64.shiftRight @UInt64.shiftRight_zero, Folder.leftAnnihilator (0 : UInt64) 0 UInt64.shiftRight @UInt64.zero_shiftRight]),
  (``USize.shiftRight, Folder.first #[Folder.mkBinaryUSize UInt64.shiftRight UInt32.shiftRight, Folder.rightNeutralUSize 0 0, Folder.leftAnnihilatorUSize 0 0 0 0]),

  (``Nat.land, Folder.first #[Folder.mkBinary Nat.land, Folder.leftRightAnnihilator 0 0 Nat.land, Folder.idempotent Nat.land Nat.and_self]),
  (``UInt8.land, Folder.first #[Folder.mkBinary UInt8.land, Folder.leftRightAnnihilator 0 0 UInt8.land @UInt8.zero_and @UInt8.and_zero, Folder.leftRightNeutral (-1 : UInt8) UInt8.land @UInt8.neg_one_and @UInt8.and_neg_one, Folder.idempotent UInt8.land @UInt8.and_self]),
  (``UInt16.land, Folder.first #[Folder.mkBinary UInt16.land, Folder.leftRightAnnihilator 0 0 UInt16.land @UInt16.zero_and @UInt16.and_zero, Folder.leftRightNeutral (-1 : UInt16) UInt16.land @UInt16.neg_one_and @UInt16.and_neg_one, Folder.idempotent UInt16.land @UInt16.and_self]),
  (``UInt32.land, Folder.first #[Folder.mkBinary UInt32.land, Folder.leftRightAnnihilator 0 0 UInt32.land @UInt32.zero_and @UInt32.and_zero, Folder.leftRightNeutral (-1 : UInt32) UInt32.land @UInt32.neg_one_and @UInt32.and_neg_one, Folder.idempotent UInt32.land @UInt32.and_self]),
  (``UInt64.land, Folder.first #[Folder.mkBinary UInt64.land, Folder.leftRightAnnihilator 0 0 UInt64.land @UInt64.zero_and @UInt64.and_zero, Folder.leftRightNeutral (-1 : UInt64) UInt64.land @UInt64.neg_one_and @UInt64.and_neg_one, Folder.idempotent UInt64.land @UInt64.and_self]),
  (``USize.land, Folder.first #[Folder.mkBinaryUSize UInt64.land UInt32.land, Folder.leftRightAnnihilatorUSize 0 0 0 0, Folder.leftRightNeutralUSize (-1) (-1), Folder.idempotent USize.land @USize.and_self]),

  (``Nat.lor, Folder.first #[Folder.mkBinary Nat.lor, Folder.leftRightNeutral 0 Nat.lor, Folder.idempotent Nat.lor Nat.or_self]),
  (``UInt8.lor, Folder.first #[Folder.mkBinary UInt8.lor, Folder.leftRightNeutral 0 UInt8.lor @UInt8.zero_or @UInt8.or_zero, Folder.leftRightAnnihilator (-1 : UInt8) (-1) UInt8.lor @UInt8.neg_one_or @UInt8.or_neg_one, Folder.idempotent UInt8.lor @UInt8.or_self]),
  (``UInt16.lor, Folder.first #[Folder.mkBinary UInt16.lor, Folder.leftRightNeutral 0 UInt16.lor @UInt16.zero_or @UInt16.or_zero, Folder.leftRightAnnihilator (-1 : UInt16) (-1) UInt16.lor @UInt16.neg_one_or @UInt16.or_neg_one, Folder.idempotent UInt16.lor @UInt16.or_self]),
  (``UInt32.lor, Folder.first #[Folder.mkBinary UInt32.lor, Folder.leftRightNeutral 0 UInt32.lor @UInt32.zero_or @UInt32.or_zero, Folder.leftRightAnnihilator (-1 : UInt32) (-1) UInt32.lor @UInt32.neg_one_or @UInt32.or_neg_one, Folder.idempotent UInt32.lor @UInt32.or_self]),
  (``UInt64.lor, Folder.first #[Folder.mkBinary UInt64.lor, Folder.leftRightNeutral 0 UInt64.lor @UInt64.zero_or @UInt64.or_zero, Folder.leftRightAnnihilator (-1 : UInt64) (-1) UInt64.lor @UInt64.neg_one_or @UInt64.or_neg_one, Folder.idempotent UInt64.lor @UInt64.or_self]),
  (``USize.lor, Folder.first #[Folder.mkBinaryUSize UInt64.lor UInt32.lor, Folder.leftRightNeutralUSize 0 0, Folder.leftRightAnnihilatorUSize (-1) (-1) (-1) (-1), Folder.idempotent USize.lor @USize.or_self]),

  (``Nat.xor, Folder.first #[Folder.mkBinary Nat.xor, Folder.leftRightNeutral 0 Nat.xor, Folder.sameArg 0 Nat.xor Nat.xor_self]),
  (``UInt8.xor, Folder.first #[Folder.mkBinary UInt8.xor, Folder.leftRightNeutral 0 UInt8.xor @UInt8.zero_xor @UInt8.xor_zero, Folder.sameArg (0 : UInt8) UInt8.xor @UInt8.xor_self]),
  (``UInt16.xor, Folder.first #[Folder.mkBinary UInt16.xor, Folder.leftRightNeutral 0 UInt16.xor @UInt16.zero_xor @UInt16.xor_zero, Folder.sameArg (0 : UInt16) UInt16.xor @UInt16.xor_self]),
  (``UInt32.xor, Folder.first #[Folder.mkBinary UInt32.xor, Folder.leftRightNeutral 0 UInt32.xor @UInt32.zero_xor @UInt32.xor_zero, Folder.sameArg (0 : UInt32) UInt32.xor @UInt32.xor_self]),
  (``UInt64.xor, Folder.first #[Folder.mkBinary UInt64.xor, Folder.leftRightNeutral 0 UInt64.xor @UInt64.zero_xor @UInt64.xor_zero, Folder.sameArg (0 : UInt64) UInt64.xor @UInt64.xor_self]),
  (``USize.xor, Folder.first #[Folder.mkBinaryUSize UInt64.xor UInt32.xor, Folder.leftRightNeutralUSize 0 0, Folder.sameArgUSize 0 0]),

  (``UInt8.complement, Folder.mkUnary UInt8.complement),
  (``UInt16.complement, Folder.mkUnary UInt16.complement),
  (``UInt32.complement, Folder.mkUnary UInt32.complement),
  (``UInt64.complement, Folder.mkUnary UInt64.complement),

  (``UInt8.neg, Folder.mkUnary UInt8.neg),
  (``UInt16.neg, Folder.mkUnary UInt16.neg),
  (``UInt32.neg, Folder.mkUnary UInt32.neg),
  (``UInt64.neg, Folder.mkUnary UInt64.neg),
  (``USize.neg, Folder.mkUnaryUSize UInt64.neg UInt32.neg),

  (``Nat.pow, Folder.first #[foldNatPow, Folder.rightNeutral 1 (· ^ ·) Nat.pow_one, Folder.rightAnnihilator 0 1 (· ^ ·) Nat.pow_zero, Folder.leftAnnihilator 1 1 (· ^ ·) Nat.one_pow]),
  (``Nat.nextPowerOfTwo, Folder.mkUnary Nat.nextPowerOfTwo),
]

def relationFolders : List (Name × Folder) := [
  (``Nat.decEq, Folder.mkBinaryDecisionProcedure Nat.decEq),
  (``Nat.decLt, Folder.mkBinaryDecisionProcedure Nat.decLt),
  (``Nat.decLe, Folder.mkBinaryDecisionProcedure Nat.decLe),
  (``Nat.beq, Folder.mkBinary Nat.beq),
  (``Nat.ble, Folder.first #[Folder.mkBinary Nat.ble, Folder.leftAnnihilator 0 true Nat.ble (by simp [Nat.ble_eq, Nat.zero_le])]),
  (``Nat.blt, Folder.first #[Folder.mkBinary Nat.blt, Folder.rightAnnihilator 0 false Nat.blt (by simp [Bool.eq_false_iff, Nat.blt_eq, Nat.not_lt_zero])]),
  (``Nat.testBit, Folder.first #[Folder.mkBinary Nat.testBit, Folder.leftAnnihilator 0 false Nat.testBit Nat.zero_testBit]),
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
  (``USize.decEq, Folder.mkBinaryUSizeDecisionProcedure UInt64.decEq UInt32.decEq),
  (``USize.decLt, Folder.mkBinaryUSizeDecisionProcedure UInt64.decLt UInt32.decLt),
  (``USize.decLe, Folder.mkBinaryUSizeDecisionProcedure UInt64.decLe UInt32.decLe),
  (``Bool.decEq, Folder.mkBinaryDecisionProcedure Bool.decEq),
  (``String.decEq, Folder.mkBinaryDecisionProcedure String.decEq)
]

def conversionFolders : List (Name × Folder) := [
  (``UInt8.ofNat, Folder.ofNat (fun v => .uint8 (UInt8.ofNat v))),
  (``UInt16.ofNat, Folder.ofNat (fun v => .uint16 (UInt16.ofNat v))),
  (``UInt32.ofNat, Folder.ofNat (fun v => .uint32 (UInt32.ofNat v))),
  (``UInt64.ofNat, Folder.ofNat (fun v => .uint64 (UInt64.ofNat v))),
  (``USize.ofNat, Folder.ofNat (fun v => .usize (UInt64.ofNat v))),
  (``Char.ofNat, Folder.charOfNat),
  (``UInt8.ofNatLT, Folder.ofNatLT (fun v => .uint8 (UInt8.ofNat v))),
  (``UInt16.ofNatLT, Folder.ofNatLT (fun v => .uint16 (UInt16.ofNat v))),
  (``UInt32.ofNatLT, Folder.ofNatLT (fun v => .uint32 (UInt32.ofNat v))),
  (``UInt64.ofNatLT, Folder.ofNatLT (fun v => .uint64 (UInt64.ofNat v))),
  (``UInt8.toNat, Folder.toNat),
  (``UInt16.toNat, Folder.toNat),
  (``UInt32.toNat, Folder.toNat),
  (``UInt64.toNat, Folder.toNat),
  (``USize.toNat, Folder.toNat),
  (``UInt8.ofNatClamp, Folder.mkUnary UInt8.ofNatClamp),
  (``UInt16.ofNatClamp, Folder.mkUnary UInt16.ofNatClamp),
  (``UInt32.ofNatClamp, Folder.mkUnary UInt32.ofNatClamp),
  (``UInt64.ofNatClamp, Folder.mkUnary UInt64.ofNatClamp),
  (``USize.ofNatClamp, Folder.mkUnaryToUSize UInt64.ofNatClamp UInt32.ofNatClamp),
  (``UInt8.toUInt16, Folder.mkUnary UInt8.toUInt16),
  (``UInt8.toUInt32, Folder.mkUnary UInt8.toUInt32),
  (``UInt8.toUInt64, Folder.mkUnary UInt8.toUInt64),
  (``UInt8.toUSize, Folder.mkUnaryToUSize UInt8.toUInt64 UInt8.toUInt32),
  (``UInt16.toUInt8, Folder.mkUnary UInt16.toUInt8),
  (``UInt16.toUInt32, Folder.mkUnary UInt16.toUInt32),
  (``UInt16.toUInt64, Folder.mkUnary UInt16.toUInt64),
  (``UInt16.toUSize, Folder.mkUnaryToUSize UInt16.toUInt64 UInt16.toUInt32),
  (``UInt32.toUInt8, Folder.mkUnary UInt32.toUInt8),
  (``UInt32.toUInt16, Folder.mkUnary UInt32.toUInt16),
  (``UInt32.toUInt64, Folder.mkUnary UInt32.toUInt64),
  (``UInt32.toUSize, Folder.mkUnaryToUSize UInt32.toUInt64 id),
  (``UInt64.toUInt8, Folder.mkUnary UInt64.toUInt8),
  (``UInt64.toUInt16, Folder.mkUnary UInt64.toUInt16),
  (``UInt64.toUInt32, Folder.mkUnary UInt64.toUInt32),
  (``UInt64.toUSize, Folder.mkUnaryToUSize id UInt64.toUInt32),
  (``USize.toUInt8, Folder.mkUnaryOfUSize UInt64.toUInt8 UInt32.toUInt8),
  (``USize.toUInt16, Folder.mkUnaryOfUSize UInt64.toUInt16 UInt32.toUInt16),
  (``USize.toUInt32, Folder.mkUnaryOfUSize UInt64.toUInt32 id),
  (``USize.toUInt64, Folder.mkUnaryOfUSize id UInt32.toUInt64),
  (``Bool.toNat, Folder.mkUnary Bool.toNat),
  (``Bool.toUInt8, Folder.mkUnary Bool.toUInt8),
  (``Bool.toUInt16, Folder.mkUnary Bool.toUInt16),
  (``Bool.toUInt32, Folder.mkUnary Bool.toUInt32),
  (``Bool.toUInt64, Folder.mkUnary Bool.toUInt64),
  (``Bool.toUSize, Folder.mkUnaryToUSize Bool.toUInt64 Bool.toUInt32),
]

/--
All string folders.
-/
def stringFolders : List (Name × Folder) := [
  (``String.append, Folder.first #[Folder.mkBinary String.append, Folder.leftRightNeutral "" (· ++ ·)]),
  (``String.length, Folder.mkUnary String.length),
  (``String.push, Folder.mkBinary String.push),
  (``String.hash, Folder.mkUnary String.hash),
  (``String.utf8ByteSize, Folder.mkUnary String.utf8ByteSize)
]

def hashFolders : List (Name × Folder) := [
  (``mixHash, Folder.mkBinary mixHash)
]

def foldTaskGet (args : Array (Arg .pure)) : FolderM (Option (LetValue .pure)) := do
  let #[_, .fvar taskFVar] := args | return none
  let some (.const ``Task.pure _ #[_, val]) ← findLetValue? (pu := .pure) taskFVar | return none
  match val with
  | .erased => return some .erased
  | .fvar fvarId => return some (.fvar fvarId #[])
  | _ => return none

def taskFolders : List (Name × Folder) := [
  (``Task.get, foldTaskGet)
]

def charFolders : List (Name × Folder) := [
  (``Char.utf8Size, Folder.mkUnary Char.utf8Size)
]

/--
Apply all known folders to `decl`.
-/
def applyFolders (decl : LetDecl .pure) (folders : SMap Name Folder) : CompilerM (Option (Array (CodeDecl .pure))) := do
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
  (arithmeticFolders
    ++ relationFolders
    ++ conversionFolders
    ++ higherOrderLiteralFolders
    ++ stringFolders
    ++ hashFolders
    ++ charFolders
    ++ taskFolders).foldl (init := {}) fun s (declName, folder) =>
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
      let newEntries := takeNewEntries newState.1 oldState.1
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
def foldConstants (decl : LetDecl .pure) : CompilerM (Option (Array (CodeDecl .pure))) := do
  applyFolders decl (← getFolders)

end ConstantFold
end Lean.Compiler.LCNF.Simp

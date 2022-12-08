/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

/-! Constant folding for primitives that have special runtime support. -/

namespace Lean.Compiler

def mkLcProof (p : Expr) :=
  mkApp (mkConst ``lcProof []) p

abbrev BinFoldFn := Bool → Expr → Expr → Option Expr
abbrev UnFoldFn  := Bool → Expr → Option Expr

def mkUIntTypeName (nbytes : Nat) : Name :=
  Name.mkSimple ("UInt" ++ toString nbytes)

structure NumScalarTypeInfo where
  nbits : Nat
  id : Name      := mkUIntTypeName nbits
  ofNatFn : Name := Name.mkStr id "ofNat"
  toNatFn : Name := Name.mkStr id "toNat"
  size : Nat     := 2^nbits

def numScalarTypes : List NumScalarTypeInfo :=
  [{nbits := 8}, {nbits := 16}, {nbits := 32}, {nbits := 64},
   {id := ``USize, nbits := System.Platform.numBits}]

def isOfNat (fn : Name) : Bool :=
  numScalarTypes.any (fun info => info.ofNatFn == fn)

def isToNat (fn : Name) : Bool :=
  numScalarTypes.any (fun info => info.toNatFn == fn)

def getInfoFromFn (fn : Name) : List NumScalarTypeInfo → Option NumScalarTypeInfo
  | []          => none
  | info::infos =>
    if info.ofNatFn == fn then some info
    else getInfoFromFn fn infos

def getInfoFromVal : Expr → Option NumScalarTypeInfo
  | Expr.app (Expr.const fn _) _ => getInfoFromFn fn numScalarTypes
  | _                            => none

@[export lean_get_num_lit]
def getNumLit : Expr → Option Nat
  | Expr.lit (Literal.natVal n)  => some n
  | Expr.app (Expr.const fn _) a => if isOfNat fn then getNumLit a else none
  | _                            => none

def mkUIntLit (info : NumScalarTypeInfo) (n : Nat) : Expr :=
  mkApp (mkConst info.ofNatFn) (mkRawNatLit (n%info.size))

def mkUInt32Lit (n : Nat) : Expr :=
  mkUIntLit {nbits := 32} n

def foldBinUInt (fn : NumScalarTypeInfo → Bool → Nat → Nat → Nat) (beforeErasure : Bool) (a₁ a₂ : Expr) : Option Expr := do
  let n₁   ← getNumLit a₁
  let n₂   ← getNumLit a₂
  let info ← getInfoFromVal a₁
  return mkUIntLit info (fn info beforeErasure n₁ n₂)

def foldUIntAdd := foldBinUInt fun _ _ => Add.add
def foldUIntMul := foldBinUInt fun _ _ => Mul.mul
def foldUIntDiv := foldBinUInt fun _ _ => Div.div
def foldUIntMod := foldBinUInt fun _ _ => Mod.mod
def foldUIntSub := foldBinUInt fun info _ a b => (a + (info.size - b))

def preUIntBinFoldFns : List (Name × BinFoldFn) :=
  [(`add, foldUIntAdd), (`mul, foldUIntMul), (`div, foldUIntDiv),
   (`mod, foldUIntMod), (`sub, foldUIntSub)]

def uintBinFoldFns : List (Name × BinFoldFn) :=
  numScalarTypes.foldl (fun r info => r ++ (preUIntBinFoldFns.map (fun ⟨suffix, fn⟩ => (info.id ++ suffix, fn)))) []

def foldNatBinOp (fn : Nat → Nat → Nat) (a₁ a₂ : Expr) : Option Expr := do
  let n₁   ← getNumLit a₁
  let n₂   ← getNumLit a₂
  return mkRawNatLit (fn n₁ n₂)

def foldNatAdd (_ : Bool) := foldNatBinOp Add.add
def foldNatMul (_ : Bool) := foldNatBinOp Mul.mul
def foldNatDiv (_ : Bool) := foldNatBinOp Div.div
def foldNatMod (_ : Bool) := foldNatBinOp Mod.mod

-- TODO: add option for controlling the limit
def natPowThreshold := 256

def foldNatPow (_ : Bool) (a₁ a₂ : Expr) : Option Expr := do
  let n₁   ← getNumLit a₁
  let n₂   ← getNumLit a₂
  if n₂ < natPowThreshold then
    return mkRawNatLit (n₁ ^ n₂)
  else
    failure

def mkNatEq (a b : Expr) : Expr :=
  mkAppN (mkConst ``Eq [levelOne]) #[(mkConst `Nat), a, b]

def mkNatLt (a b : Expr) : Expr :=
  mkAppN (mkConst ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``Nat.lt, a, b]

def mkNatLe (a b : Expr) : Expr :=
  mkAppN (mkConst ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``Nat.le, a, b]

def toDecidableExpr (beforeErasure : Bool) (pred : Expr) (r : Bool) : Expr :=
  match beforeErasure, r with
  | false, true  => mkConst ``Bool.true
  | false, false => mkConst ``Bool.false
  | true,  true  => mkDecIsTrue pred (mkLcProof pred)
  | true,  false => mkDecIsFalse pred (mkLcProof pred)

def foldNatBinPred (mkPred : Expr → Expr → Expr) (fn : Nat → Nat → Bool)
    (beforeErasure : Bool) (a₁ a₂ : Expr) : Option Expr := do
  let n₁   ← getNumLit a₁
  let n₂   ← getNumLit a₂
  return toDecidableExpr beforeErasure (mkPred a₁ a₂) (fn n₁ n₂)

def foldNatDecEq := foldNatBinPred mkNatEq (fun a b => a = b)
def foldNatDecLt := foldNatBinPred mkNatLt (fun a b => a < b)
def foldNatDecLe := foldNatBinPred mkNatLe (fun a b => a ≤ b)

def foldNatBinBoolPred (fn : Nat → Nat → Bool) (a₁ a₂ : Expr) : Option Expr := do
  let n₁   ← getNumLit a₁
  let n₂   ← getNumLit a₂
  if fn n₁ n₂ then
    return mkConst ``Bool.true
  else
    return mkConst ``Bool.false

def foldNatBeq := fun _ : Bool => foldNatBinBoolPred (fun a b => a == b)
def foldNatBle := fun _ : Bool => foldNatBinBoolPred (fun a b => a < b)
def foldNatBlt := fun _ : Bool => foldNatBinBoolPred (fun a b => a ≤ b)

def natFoldFns : List (Name × BinFoldFn) :=
  [(``Nat.add, foldNatAdd),
   (``Nat.mul, foldNatMul),
   (``Nat.div, foldNatDiv),
   (``Nat.mod, foldNatMod),
   (``Nat.pow, foldNatPow),
   (``Nat.decEq, foldNatDecEq),
   (``Nat.decLt, foldNatDecLt),
   (``Nat.decLe, foldNatDecLe),
   (``Nat.beq,   foldNatBeq),
   (``Nat.blt,   foldNatBlt),
   (``Nat.ble,   foldNatBle)
]

def getBoolLit : Expr → Option Bool
  | Expr.const ``Bool.true _  => some true
  | Expr.const ``Bool.false _ => some false
  | _                         => none

def foldStrictAnd (_ : Bool) (a₁ a₂ : Expr) : Option Expr :=
  let v₁ := getBoolLit a₁
  let v₂ := getBoolLit a₂
  match v₁, v₂ with
  | some true,  _ => a₂
  | some false, _ => a₁
  | _, some true  => a₁
  | _, some false => a₂
  | _, _          => none

def foldStrictOr (_ : Bool) (a₁ a₂ : Expr) : Option Expr :=
  let v₁ := getBoolLit a₁
  let v₂ := getBoolLit a₂
  match v₁, v₂ with
  | some true,  _ => a₁
  | some false, _ => a₂
  | _, some true  => a₂
  | _, some false => a₁
  | _, _          => none

def boolFoldFns : List (Name × BinFoldFn) :=
  [(``strictOr, foldStrictOr), (``strictAnd, foldStrictAnd)]

def binFoldFns : List (Name × BinFoldFn) :=
  boolFoldFns ++ uintBinFoldFns ++ natFoldFns

def foldNatSucc (_ : Bool) (a : Expr) : Option Expr := do
  let n ← getNumLit a
  return mkRawNatLit (n+1)

def foldCharOfNat (beforeErasure : Bool) (a : Expr) : Option Expr := do
  guard (!beforeErasure)
  let n ← getNumLit a
  if isValidChar n.toUInt32 then
    return mkUInt32Lit n
  else
    return mkUInt32Lit 0

def foldToNat (_ : Bool) (a : Expr) : Option Expr := do
  let n ← getNumLit a
  return mkRawNatLit n

def uintFoldToNatFns : List (Name × UnFoldFn) :=
  numScalarTypes.foldl (fun r info => (info.toNatFn, foldToNat) :: r) []

def unFoldFns : List (Name × UnFoldFn) :=
  [(``Nat.succ, foldNatSucc),
   (``Char.ofNat, foldCharOfNat)]
  ++ uintFoldToNatFns

def findBinFoldFn (fn : Name) : Option BinFoldFn :=
  binFoldFns.lookup fn

def findUnFoldFn (fn : Name) : Option UnFoldFn :=
  unFoldFns.lookup fn

@[export lean_fold_bin_op]
def foldBinOp (beforeErasure : Bool) (f : Expr) (a : Expr) (b : Expr) : Option Expr := do
  match f with
  | Expr.const fn _ =>
     let foldFn ← findBinFoldFn fn
     foldFn beforeErasure a b
  | _ =>
    failure

@[export lean_fold_un_op]
def foldUnOp (beforeErasure : Bool) (f : Expr) (a : Expr) : Option Expr := do
  match f with
  | Expr.const fn _ =>
     let foldFn ← findUnFoldFn fn
     foldFn beforeErasure a
  | _ => failure

end Lean.Compiler

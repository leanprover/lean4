/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.System.Platform
import Init.Lean.Expr
import Init.Lean.Compiler.Util

/- Constant folding for primitives that have special runtime support. -/

namespace Lean
namespace Compiler

def BinFoldFn := Bool → Expr → Expr → Option Expr
def UnFoldFn  := Bool → Expr → Option Expr

def mkUIntTypeName (nbytes : Nat) : Name :=
mkSimpleName ("UInt" ++ toString nbytes)

structure NumScalarTypeInfo :=
(nbits : Nat)
(id : Name      := mkUIntTypeName nbits)
(ofNatFn : Name := Name.mkString id "ofNat")
(toNatFn : Name := Name.mkString id "toNat")
(size : Nat     := 2^nbits)

def numScalarTypes : List NumScalarTypeInfo :=
[{nbits := 8}, {nbits := 16}, {nbits := 32}, {nbits := 64},
 {id := `USize, nbits := System.Platform.numBits}]

def isOfNat (fn : Name) : Bool :=
numScalarTypes.any (fun info => info.ofNatFn = fn)

def isToNat (fn : Name) : Bool :=
numScalarTypes.any (fun info => info.toNatFn = fn)

def getInfoFromFn (fn : Name) : List NumScalarTypeInfo → Option NumScalarTypeInfo
| []          => none
| info::infos =>
  if info.ofNatFn = fn then some info
  else getInfoFromFn infos

def getInfoFromVal : Expr → Option NumScalarTypeInfo
| Expr.app (Expr.const fn _) _   => getInfoFromFn fn numScalarTypes
| _ => none

@[export lean_get_num_lit]
def getNumLit : Expr → Option Nat
| Expr.lit (Literal.natVal n)  => some n
| Expr.app (Expr.const fn _) a => if isOfNat fn then getNumLit a else none
| _                            => none

def mkUIntLit (info : NumScalarTypeInfo) (n : Nat) : Expr :=
mkApp (mkConst info.ofNatFn) (mkNatLit (n%info.size))

def mkUInt32Lit (n : Nat) : Expr :=
mkUIntLit {nbits := 32} n

def foldBinUInt (fn : NumScalarTypeInfo → Bool → Nat → Nat → Nat) (beforeErasure : Bool) (a₁ a₂ : Expr) : Option Expr :=
do n₁   ← getNumLit a₁;
   n₂   ← getNumLit a₂;
   info ← getInfoFromVal a₁;
   pure $ mkUIntLit info (fn info beforeErasure n₁ n₂)

def foldUIntAdd := foldBinUInt $ fun _ _ => HasAdd.add
def foldUIntMul := foldBinUInt $ fun _ _ => HasMul.mul
def foldUIntDiv := foldBinUInt $ fun _ _ => HasDiv.div
def foldUIntMod := foldBinUInt $ fun _ _ => HasMod.mod
def foldUIntSub := foldBinUInt $ fun info _ a b => (a + (info.size - b))

def preUIntBinFoldFns : List (Name × BinFoldFn) :=
[(`add, foldUIntAdd), (`mul, foldUIntMul), (`div, foldUIntDiv),
 (`mod, foldUIntMod), (`sub, foldUIntSub)]

def uintBinFoldFns : List (Name × BinFoldFn) :=
numScalarTypes.foldl (fun r info => r ++ (preUIntBinFoldFns.map (fun ⟨suffix, fn⟩ => (info.id ++ suffix, fn)))) []

def foldNatBinOp (fn : Nat → Nat → Nat) (a₁ a₂ : Expr) : Option Expr :=
do n₁   ← getNumLit a₁;
   n₂   ← getNumLit a₂;
   pure $ mkNatLit (fn n₁ n₂)

def foldNatAdd (_ : Bool) := foldNatBinOp HasAdd.add
def foldNatMul (_ : Bool) := foldNatBinOp HasMul.mul
def foldNatDiv (_ : Bool) := foldNatBinOp HasDiv.div
def foldNatMod (_ : Bool) := foldNatBinOp HasMod.mod
def foldNatPow (_ : Bool) := foldNatBinOp HasPow.pow

def mkNatEq (a b : Expr) : Expr :=
mkAppN (mkConst `Eq [Level.one]) #[(mkConst `Nat), a, b]

def mkNatLt (a b : Expr) : Expr :=
mkAppN (mkConst `HasLt.lt [Level.zero]) #[mkConst `Nat, mkConst `Nat.HasLt, a, b]

def mkNatLe (a b : Expr) : Expr :=
mkAppN (mkConst `HasLt.le [Level.zero]) #[mkConst `Nat, mkConst `Nat.HasLe, a, b]

def toDecidableExpr (beforeErasure : Bool) (pred : Expr) (r : Bool) : Expr :=
match beforeErasure, r with
| false, true  => mkDecIsTrue  neutralExpr neutralExpr
| false, false => mkDecIsFalse neutralExpr neutralExpr
| true,  true  => mkDecIsTrue pred (mkLcProof pred)
| true,  false => mkDecIsFalse pred (mkLcProof pred)

def foldNatBinPred (mkPred : Expr → Expr → Expr) (fn : Nat → Nat → Bool)
                      (beforeErasure : Bool) (a₁ a₂ : Expr) : Option Expr :=
do n₁   ← getNumLit a₁;
   n₂   ← getNumLit a₂;
   pure $ toDecidableExpr beforeErasure (mkPred a₁ a₂) (fn n₁ n₂)

def foldNatDecEq := foldNatBinPred mkNatEq (fun a b => a = b)
def foldNatDecLt := foldNatBinPred mkNatLt (fun a b => a < b)
def foldNatDecLe := foldNatBinPred mkNatLe (fun a b => a ≤ b)

def natFoldFns : List (Name × BinFoldFn) :=
[(`Nat.add, foldNatAdd),
 (`Nat.mul, foldNatMul),
 (`Nat.div, foldNatDiv),
 (`Nat.mod, foldNatMod),
 (`Nat.pow, foldNatPow),
 (`Nat.pow._main, foldNatPow),
 (`Nat.decEq, foldNatDecEq),
 (`Nat.decLt, foldNatDecLt),
 (`Nat.decLe, foldNatDecLe)]

def getBoolLit : Expr → Option Bool
| Expr.const `Bool.true _  => some true
| Expr.const `Bool.false _ => some false
| _                        => none

def foldStrictAnd (_ : Bool) (a₁ a₂ : Expr) : Option Expr :=
let v₁ := getBoolLit a₁;
let v₂ := getBoolLit a₂;
match v₁, v₂ with
| some true,  _ => a₂
| some false, _ => a₁
| _, some true  => a₁
| _, some false => a₂
| _, _          => none

def foldStrictOr (_ : Bool) (a₁ a₂ : Expr) : Option Expr :=
let v₁ := getBoolLit a₁;
let v₂ := getBoolLit a₂;
match v₁, v₂ with
| some true,  _ => a₁
| some false, _ => a₂
| _, some true  => a₂
| _, some false => a₁
| _, _          => none

def boolFoldFns : List (Name × BinFoldFn) :=
[(`strictOr, foldStrictOr), (`strictAnd, foldStrictAnd)]

def binFoldFns : List (Name × BinFoldFn) :=
boolFoldFns ++ uintBinFoldFns ++ natFoldFns

def foldNatSucc (_ : Bool) (a : Expr) : Option Expr :=
do n   ← getNumLit a;
   pure $ mkNatLit (n+1)

def foldCharOfNat (beforeErasure : Bool) (a : Expr) : Option Expr :=
do guard (!beforeErasure);
   n ← getNumLit a;
   pure $
     if isValidChar n.toUInt32 then mkUInt32Lit n
     else mkUInt32Lit 0

def foldToNat (_ : Bool) (a : Expr) : Option Expr :=
do n ← getNumLit a;
   pure $ mkNatLit n

def uintFoldToNatFns : List (Name × UnFoldFn) :=
numScalarTypes.foldl (fun r info => (info.toNatFn, foldToNat) :: r) []

def unFoldFns : List (Name × UnFoldFn) :=
[(`Nat.succ, foldNatSucc),
 (`Char.ofNat, foldCharOfNat)]
++ uintFoldToNatFns

def findBinFoldFn (fn : Name) : Option BinFoldFn :=
binFoldFns.lookup fn

def findUnFoldFn (fn : Name) : Option UnFoldFn :=
unFoldFns.lookup fn

@[export lean_fold_bin_op]
def foldBinOp (beforeErasure : Bool) (f : Expr) (a : Expr) (b : Expr) : Option Expr :=
match f with
| Expr.const fn _ => do
   foldFn ← findBinFoldFn fn;
   foldFn beforeErasure a b
| _ => none

@[export lean_fold_un_op]
def foldUnOp (beforeErasure : Bool) (f : Expr) (a : Expr) : Option Expr :=
match f with
| Expr.const fn _ => do
   foldFn ← findUnFoldFn fn;
   foldFn beforeErasure a
| _ => none

end Compiler
end Lean

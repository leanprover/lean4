/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr init.platform
import init.lean.compiler.util

/- Constant folding for primitives that have special runtime support. -/

namespace Lean
namespace Compiler

def BinFoldFn := Bool → Expr → Expr → Option Expr
def UnFoldFn  := Bool → Expr → Option Expr

def mkUIntTypeName (nbytes : Nat) : Name :=
mkSimpleName ("UInt" ++ toString nbytes)

structure NumScalarTypeInfo :=
(nbits : Nat)
(id : Name        := mkUIntTypeName nbits)
(ofNatFn : Name := Name.mkString id "ofNat")
(size : Nat       := 2^nbits)

def numScalarTypes : List NumScalarTypeInfo :=
[{nbits := 8}, {nbits := 16}, {nbits := 32}, {nbits := 64},
 {id := `Usize, nbits := System.platform.nbits}]

def isOfNat (fn : Name) : Bool :=
numScalarTypes.any (λ info, info.ofNatFn = fn)

def getInfoFromFn (fn : Name) : List NumScalarTypeInfo → Option NumScalarTypeInfo
| []            := none
| (info::infos) :=
  if info.ofNatFn = fn then some info
  else getInfoFromFn infos

def getInfoFromVal : Expr → Option NumScalarTypeInfo
| (Expr.app (Expr.const fn _) _) := getInfoFromFn fn numScalarTypes
| _ := none

@[export lean.get_num_lit_core]
def getNumLit : Expr → Option Nat
| (Expr.lit (Literal.natVal n)) := some n
| (Expr.app (Expr.const fn _) a) := if isOfNat fn then getNumLit a else none
| _                              := none

def mkUIntLit (info : NumScalarTypeInfo) (n : Nat) : Expr :=
Expr.app (Expr.const info.ofNatFn []) (Expr.lit (Literal.natVal (n%info.size)))

def mkUInt32Lit (n : Nat) : Expr :=
mkUIntLit {nbits := 32} n

def foldBinUInt (fn : NumScalarTypeInfo → Bool → Nat → Nat → Nat) (beforeErasure : Bool) (a₁ a₂ : Expr) : Option Expr :=
do n₁   ← getNumLit a₁,
   n₂   ← getNumLit a₂,
   info ← getInfoFromVal a₁,
   pure $ mkUIntLit info (fn info beforeErasure n₁ n₂)

def foldUIntAdd := foldBinUInt $ λ _ _, (+)
def foldUIntMul := foldBinUInt $ λ _ _, (*)
def foldUIntDiv := foldBinUInt $ λ _ _, (/)
def foldUIntMod := foldBinUInt $ λ _ _, (%)
def foldUIntSub := foldBinUInt $ λ info _ a b, (a + (info.size - b))

def preUIntBinFoldFns : List (Name × BinFoldFn) :=
[(`add, foldUIntAdd), (`mul, foldUIntMul), (`div, foldUIntDiv),
 (`mod, foldUIntMod), (`sub, foldUIntSub)]

def uintBinFoldFns : List (Name × BinFoldFn) :=
numScalarTypes.foldl (λ r info, r ++ (preUIntBinFoldFns.map (λ ⟨suffix, fn⟩, (info.id ++ suffix, fn)))) []

def foldNatBinOp (fn : Nat → Nat → Nat) (a₁ a₂ : Expr) : Option Expr :=
do n₁   ← getNumLit a₁,
   n₂   ← getNumLit a₂,
   pure $ Expr.lit (Literal.natVal (fn n₁ n₂))

def foldNatAdd (_ : Bool) := foldNatBinOp (+)
def foldNatMul (_ : Bool) := foldNatBinOp (*)
def foldNatDiv (_ : Bool) := foldNatBinOp (/)
def foldNatMod (_ : Bool) := foldNatBinOp (%)

def mkNatEq (a b : Expr) : Expr :=
mkBinApp (Expr.app (Expr.const `Eq [Level.one]) (Expr.const `Nat [])) a b

def mkNatLt (a b : Expr) : Expr :=
mkBinApp (mkBinApp (Expr.const `HasLt.lt [Level.zero]) (Expr.const `Nat []) (Expr.const `Nat.HasLt [])) a b

def mkNatLe (a b : Expr) : Expr :=
mkBinApp (mkBinApp (Expr.const `HasLt.le [Level.zero]) (Expr.const `Nat []) (Expr.const `Nat.HasLe [])) a b

def toDecidableExpr (beforeErasure : Bool) (pred : Expr) (r : Bool) : Expr :=
match beforeErasure, r with
| false, true  := mkDecIsTrue  neutralExpr neutralExpr
| false, false := mkDecIsFalse neutralExpr neutralExpr
| true,  true  := mkDecIsTrue pred (mkLcProof pred)
| true,  false := mkDecIsFalse pred (mkLcProof pred)

def foldNatBinPred (mkPred : Expr → Expr → Expr) (fn : Nat → Nat → Bool)
                      (beforeErasure : Bool) (a₁ a₂ : Expr) : Option Expr :=
do n₁   ← getNumLit a₁,
   n₂   ← getNumLit a₂,
   pure $ toDecidableExpr beforeErasure (mkPred a₁ a₂) (fn n₁ n₂)

def foldNatDecEq := foldNatBinPred mkNatEq (λ a b, a = b)
def foldNatDecLt := foldNatBinPred mkNatLt (λ a b, a < b)
def foldNatDecLe := foldNatBinPred mkNatLe (λ a b, a ≤ b)

def natFoldFns : List (Name × BinFoldFn) :=
[(`Nat.add, foldNatAdd),
 (`Nat.mul, foldNatMul),
 (`Nat.div, foldNatDiv),
 (`Nat.mod, foldNatMod),
 (`Nat.decEq, foldNatDecEq),
 (`Nat.decLt, foldNatDecLt),
 (`Nat.decLe, foldNatDecLe)]

def binFoldFns : List (Name × BinFoldFn) :=
uintBinFoldFns ++ natFoldFns

def foldNatSucc (_ : Bool) (a : Expr) : Option Expr :=
do n   ← getNumLit a,
   pure $ Expr.lit (Literal.natVal (n+1))

def foldCharOfNat (beforeErasure : Bool) (a : Expr) : Option Expr :=
do guard (!beforeErasure),
   n ← getNumLit a,
   pure $
     if isValidChar (UInt32.ofNat n) then mkUInt32Lit n
     else mkUInt32Lit 0

def unFoldFns : List (Name × UnFoldFn) :=
[(`Nat.succ, foldNatSucc),
 (`Char.ofNat, foldCharOfNat)]

-- TODO(Leo): move
private def {u} alistFind {α : Type u} (n : Name) : List (Name × α) → Option α
| []          := none
| ((k, v)::r) :=
  if n = k then some v else alistFind r

def findBinFoldFn (fn : Name) : Option BinFoldFn :=
alistFind fn binFoldFns

def findUnFoldFn (fn : Name) : Option UnFoldFn :=
alistFind fn unFoldFns

@[export lean.fold_bin_op_core]
def foldBinOp (beforeErasure : Bool) (f : Expr) (a : Expr) (b : Expr) : Option Expr :=
match f with
| Expr.const fn _ := do
   foldFn ← findBinFoldFn fn,
   foldFn beforeErasure a b
| _ := none

@[export lean.fold_un_op_core]
def foldUnOp (beforeErasure : Bool) (f : Expr) (a : Expr) : Option Expr :=
match f with
| Expr.const fn _ := do
   foldFn ← findUnFoldFn fn,
   foldFn beforeErasure a
| _ := none

end Compiler
end Lean

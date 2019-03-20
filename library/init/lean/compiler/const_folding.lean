/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr init.platform
import init.lean.compiler.util

/- Constant folding for primitives that have special runtime support. -/

namespace lean
namespace compiler

def binFoldFn := bool → expr → expr → option expr
def unFoldFn  := bool → expr → option expr

def mkUintTypeName (nbytes : nat) : name :=
mkSimpleName ("uint" ++ toString nbytes)

structure numScalarTypeInfo :=
(nbits : nat)
(id : name        := mkUintTypeName nbits)
(ofNatFn : name := name.mkString id "ofNat")
(size : nat       := 2^nbits)

def numScalarTypes : list numScalarTypeInfo :=
[{nbits := 8}, {nbits := 16}, {nbits := 32}, {nbits := 64},
 {id := `usize, nbits := system.platform.nbits}]

def isOfNat (fn : name) : bool :=
numScalarTypes.any (λ info, info.ofNatFn = fn)

def getInfoFromFn (fn : name) : list numScalarTypeInfo → option numScalarTypeInfo
| []            := none
| (info::infos) :=
  if info.ofNatFn = fn then some info
  else getInfoFromFn infos

def getInfoFromVal : expr → option numScalarTypeInfo
| (expr.app (expr.const fn _) _) := getInfoFromFn fn numScalarTypes
| _ := none

@[export lean.getNumLitCore]
def getNumLit : expr → option nat
| (expr.lit (literal.natVal n)) := some n
| (expr.app (expr.const fn _) a) := if isOfNat fn then getNumLit a else none
| _                              := none

def mkUintLit (info : numScalarTypeInfo) (n : nat) : expr :=
expr.app (expr.const info.ofNatFn []) (expr.lit (literal.natVal (n%info.size)))

def mkUint32Lit (n : nat) : expr :=
mkUintLit {nbits := 32} n

def foldBinUint (fn : numScalarTypeInfo → bool → nat → nat → nat) (beforeErasure : bool) (a₁ a₂ : expr) : option expr :=
do n₁   ← getNumLit a₁,
   n₂   ← getNumLit a₂,
   info ← getInfoFromVal a₁,
   pure $ mkUintLit info (fn info beforeErasure n₁ n₂)

def foldUintAdd := foldBinUint $ λ _ _, (+)
def foldUintMul := foldBinUint $ λ _ _, (*)
def foldUintDiv := foldBinUint $ λ _ _, (/)
def foldUintMod := foldBinUint $ λ _ _, (%)
def foldUintSub := foldBinUint $ λ info _ a b, (a + (info.size - b))

def preUintBinFoldFns : list (name × binFoldFn) :=
[(`add, foldUintAdd), (`mul, foldUintMul), (`div, foldUintDiv),
 (`mod, foldUintMod), (`sub, foldUintSub)]

def uintBinFoldFns : list (name × binFoldFn) :=
numScalarTypes.foldl (λ r info, r ++ (preUintBinFoldFns.map (λ ⟨suffix, fn⟩, (info.id ++ suffix, fn)))) []

def foldNatBinOp (fn : nat → nat → nat) (a₁ a₂ : expr) : option expr :=
do n₁   ← getNumLit a₁,
   n₂   ← getNumLit a₂,
   pure $ expr.lit (literal.natVal (fn n₁ n₂))

def foldNatAdd (_ : bool) := foldNatBinOp (+)
def foldNatMul (_ : bool) := foldNatBinOp (*)
def foldNatDiv (_ : bool) := foldNatBinOp (/)
def foldNatMod (_ : bool) := foldNatBinOp (%)

def mkNatEq (a b : expr) : expr :=
mkBinApp (expr.app (expr.const `eq [level.one]) (expr.const `nat [])) a b

def mkNatLt (a b : expr) : expr :=
mkBinApp (mkBinApp (expr.const `hasLt.lt [level.zero]) (expr.const `nat []) (expr.const `nat.hasLt [])) a b

def mkNatLe (a b : expr) : expr :=
mkBinApp (mkBinApp (expr.const `hasLt.le [level.zero]) (expr.const `nat []) (expr.const `nat.hasLe [])) a b

def toDecidableExpr (beforeErasure : bool) (pred : expr) (r : bool) : expr :=
match beforeErasure, r with
| ff, tt := mkDecIsTrue  neutralExpr neutralExpr
| ff, ff := mkDecIsFalse neutralExpr neutralExpr
| tt, tt := mkDecIsTrue pred (mkLcProof pred)
| tt, ff := mkDecIsFalse pred (mkLcProof pred)

def foldNatBinPred (mkPred : expr → expr → expr) (fn : nat → nat → bool)
                      (beforeErasure : bool) (a₁ a₂ : expr) : option expr :=
do n₁   ← getNumLit a₁,
   n₂   ← getNumLit a₂,
   pure $ toDecidableExpr beforeErasure (mkPred a₁ a₂) (fn n₁ n₂)

def foldNatDecEq := foldNatBinPred mkNatEq (λ a b, a = b)
def foldNatDecLt := foldNatBinPred mkNatLt (λ a b, a < b)
def foldNatDecLe := foldNatBinPred mkNatLe (λ a b, a ≤ b)

def natFoldFns : list (name × binFoldFn) :=
[(`nat.add, foldNatAdd),
 (`nat.mul, foldNatMul),
 (`nat.div, foldNatDiv),
 (`nat.mod, foldNatMod),
 (`nat.decEq, foldNatDecEq),
 (`nat.decLt, foldNatDecLt),
 (`nat.decLe, foldNatDecLe)]

def binFoldFns : list (name × binFoldFn) :=
uintBinFoldFns ++ natFoldFns

def foldNatSucc (_ : bool) (a : expr) : option expr :=
do n   ← getNumLit a,
   pure $ expr.lit (literal.natVal (n+1))

def foldCharOfNat (beforeErasure : bool) (a : expr) : option expr :=
do guard (!beforeErasure),
   n ← getNumLit a,
   pure $
     if isValidChar (uint32.ofNat n) then mkUint32Lit n
     else mkUint32Lit 0

def unFoldFns : list (name × unFoldFn) :=
[(`nat.succ, foldNatSucc),
 (`char.ofNat, foldCharOfNat)]

-- TODO(Leo): move
private def {u} alistFind {α : Type u} (n : name) : list (name × α) → option α
| []          := none
| ((k, v)::r) :=
  if n = k then some v else alistFind r

def findBinFoldFn (fn : name) : option binFoldFn :=
alistFind fn binFoldFns

def findUnFoldFn (fn : name) : option unFoldFn :=
alistFind fn unFoldFns

@[export lean.foldBinOpCore]
def foldBinOp (beforeErasure : bool) (f : expr) (a : expr) (b : expr) : option expr :=
match f with
| expr.const fn _ := do
   foldFn ← findBinFoldFn fn,
   foldFn beforeErasure a b
| _ := none

@[export lean.foldUnOpCore]
def foldUnOp (beforeErasure : bool) (f : expr) (a : expr) : option expr :=
match f with
| expr.const fn _ := do
   foldFn ← findUnFoldFn fn,
   foldFn beforeErasure a
| _ := none

end compiler
end lean

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Message
import Std.Internal.Rat

namespace Lean.Meta.Grind.Arith

/-- Returns `true` if `e` is of the form `Nat` -/
def isNatType (e : Expr) : Bool :=
  e.isConstOf ``Nat

/-- Returns `true` if `e` is of the form `Int` -/
def isIntType (e : Expr) : Bool :=
  e.isConstOf ``Int

/-- Returns `true` if `e` is of the form `@instHAdd Nat instAddNat` -/
def isInstAddNat (e : Expr) : Bool :=
  let_expr instHAdd a b := e | false
  isNatType a && b.isConstOf ``instAddNat

/-- Returns `true` if `e` is `instLENat` -/
def isInstLENat (e : Expr) : Bool :=
  e.isConstOf ``instLENat

/--
Returns `some (a, b)` if `e` is of the form
```
@HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) a b
```
-/
def isNatAdd? (e : Expr) : Option (Expr × Expr) :=
  let_expr HAdd.hAdd _ _ _ i a b := e | none
  if isInstAddNat i then some (a, b) else none

/--
Returns `true` if `e` is of the form
```
@HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) _ _
```
-/
def isNatAdd (e : Expr) : Bool :=
  let_expr HAdd.hAdd _ _ _ i _ _ := e | false
  isInstAddNat i

/-- Returns `some k` if `e` `@OfNat.ofNat Nat _ (instOfNatNat k)` -/
def isNatNum? (e : Expr) : Option Nat := Id.run do
  let_expr OfNat.ofNat _ _ inst := e | none
  let_expr instOfNatNat k := inst | none
  let .lit (.natVal k) := k | none
  some k

def isSupportedType (e : Expr) : Bool :=
  isNatType e || isIntType e

partial def isRelevantPred (e : Expr) : Bool :=
  match_expr e with
  | Not p => isRelevantPred p
  | LE.le α _ _ _ => isSupportedType α
  | Eq α _ _ => isSupportedType α
  | Dvd.dvd α _ _ _ => isSupportedType α
  | _ => false

def isArithTerm (e : Expr) : Bool :=
  match_expr e with
  | HAdd.hAdd _ _ _ _ _ _ => true
  | HSub.hSub _ _ _ _ _ _ => true
  | HMul.hMul _ _ _ _ _ _ => true
  | HDiv.hDiv _ _ _ _ _ _ => true
  | HMod.hMod _ _ _ _ _ _ => true
  | HPow.hPow _ _ _ _ _ _ => true
  | Neg.neg _ _ _ => true
  | OfNat.ofNat _ _ _ => true
  | _ => false

/-- Quote `e` using `「` and `」` if `e` is an arithmetic term that is being treated as a variable. -/
def quoteIfArithTerm (e : Expr) : MessageData :=
  if isArithTerm e then
    aquote e
  else
    e
/--
`gcdExt a b` returns the triple `(g, α, β)` such that
- `g = gcd a b` (with `g ≥ 0`), and
- `g = α * a + β * β`.
-/
partial def gcdExt (a b : Int) : Int × Int × Int :=
  if b = 0 then
    (a.natAbs, if a = 0 then 0 else a / a.natAbs, 0)
  else
    let (g, α, β) := gcdExt b (a % b)
    (g, β, α - (a / b) * β)

open Std.Internal

-- TODO: PArray.shrink and PArray.resize
partial def shrink (a : PArray Rat) (sz : Nat) : PArray Rat :=
  if a.size > sz then shrink a.pop sz else a

partial def resize (a : PArray Rat) (sz : Nat) : PArray Rat :=
  if a.size > sz then shrink a sz else go a
where
  go (a : PArray Rat) : PArray Rat :=
    if a.size < sz then go (a.push 0) else a

namespace CollectDecVars
/-! Helper monad for collecting decision variables in `linarith` and `cutsat` -/

structure State where
  visited : Std.HashSet UInt64 := {}
  found : FVarIdSet := {}

abbrev CollectDecVarsM := ReaderT FVarIdSet $ StateM State

def alreadyVisited (c : α) : CollectDecVarsM Bool := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if (← get).visited.contains addr then return true
  modify fun s => { s with visited := s.visited.insert addr }
  return false

def markAsFound (fvarId : FVarId) : CollectDecVarsM Unit := do
  modify fun s => { s with found := s.found.insert fvarId }

abbrev CollectDecVarsM.run (x : CollectDecVarsM Unit) (decVars : FVarIdSet) : FVarIdSet :=
  let (_, s) := x decVars |>.run {}
  s.found

end CollectDecVars

export CollectDecVars (CollectDecVarsM)

end Lean.Meta.Grind.Arith

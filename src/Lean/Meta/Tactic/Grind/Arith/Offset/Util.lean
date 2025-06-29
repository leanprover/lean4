/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Message
import Lean.Meta.Tactic.Grind.Arith.Util

namespace Lean.Meta.Grind.Arith.Offset

/-- Returns `some (a, k)` if `e` is of the form `a + k`.  -/
def isNatOffset? (e : Expr) : Option (Expr × Nat) := Id.run do
  let some (a, b) := isNatAdd? e | none
  let some k := isNatNum? b | none
  some (a, k)

/-- An offset constraint. -/
structure Cnstr (α : Type) where
  u  : α
  v  : α
  k  : Int := 0
  deriving Inhabited

def Cnstr.neg : Cnstr α → Cnstr α
  | { u, v, k } => { u := v, v := u, k := -k - 1 }

example (c : Cnstr α) : c.neg.neg = c := by
  cases c; simp [Cnstr.neg]; omega

def toMessageData [inst : ToMessageData α] (c : Cnstr α) : MessageData :=
  match c.k with
  | .ofNat 0   => m!"{c.u} ≤ {c.v}"
  | .ofNat k   => m!"{c.u} ≤ {c.v} + {k}"
  | .negSucc k => m!"{c.u} + {k + 1} ≤ {c.v}"

instance : ToMessageData (Cnstr Expr) where
  toMessageData c := Offset.toMessageData c

/--
Returns `some cnstr` if `e` is offset constraint.
Remark: `z` is `0` numeral. It is an extra argument because we
want to be able to provide the one that has already been internalized.
-/
def isNatOffsetCnstr? (e : Expr) (z : Expr) : Option (Cnstr Expr) :=
  match_expr e with
  | LE.le _ inst a b => if isInstLENat inst then go a b else none
  | _ => none
where
  go (u v : Expr) :=
    if let some (u, k) := isNatOffset? u then
      some { u, k := - k, v }
    else if let some (v, k) := isNatOffset? v then
      some { u, v, k }
    else if let some k := isNatNum? u then
      some { u := z, v, k := - k }
    else if let some k := isNatNum? v then
      some { u, v := z, k }
    else
      some { u, v }

end Lean.Meta.Grind.Arith.Offset

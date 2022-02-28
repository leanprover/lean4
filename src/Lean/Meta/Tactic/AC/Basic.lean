/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import Init.Core

namespace Lean.Meta.AC
inductive Expr
  | var (x : Nat)
  | op (lhs rhs : Expr)
  deriving Inhabited, Repr, BEq

structure Variable (op : α → α → α) where
  value : α
  neutral : Option $ IsNeutral op value

structure Context (α : Type u) where
  op : α → α → α
  assoc : IsAssociative op
  comm : Option $ IsCommutative op
  idem : Option $ IsIdempotent op
  vars : List (Variable op)
  arbitrary : α

class ContextInformation (α : Type u) where
  isNeutral : α → Nat → Bool
  isComm : α → Bool
  isIdem : α → Bool

class EvalInformation (α : Type u) (β : Type v) where
  arbitrary : α → β
  evalOp : α → β → β → β
  evalVar : α → Nat → β

def Context.var (ctx : Context α) (idx : Nat) : Variable ctx.op :=
  ctx.vars.getD idx ⟨ctx.arbitrary, none⟩

instance : ContextInformation (Context α) where
  isNeutral ctx x := ctx.var x |>.neutral.isSome
  isComm ctx := ctx.comm.isSome
  isIdem ctx := ctx.idem.isSome

instance : EvalInformation (Context α) α where
  arbitrary ctx := ctx.arbitrary
  evalOp ctx := ctx.op
  evalVar ctx idx := ctx.var idx |>.value

def eval (β : Type u) [EvalInformation α β] (ctx : α) : (ex : Expr) → β
  | Expr.var idx => EvalInformation.evalVar ctx idx
  | Expr.op l r => EvalInformation.evalOp ctx (eval β ctx l) (eval β ctx r)

def Expr.toList : Expr → List Nat
  | Expr.var idx => [idx]
  | Expr.op l r => l.toList.append r.toList

def evalList (β : Type u) [EvalInformation α β] (ctx : α) : List Nat → β
  | [] => EvalInformation.arbitrary ctx
  | [x] => EvalInformation.evalVar ctx x
  | x :: xs => EvalInformation.evalOp ctx (EvalInformation.evalVar ctx x) (evalList β ctx xs)

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a :: as => if x < a then x :: a :: as else a :: insert x as

def sort (xs : List Nat) : List Nat :=
  let rec loop : List Nat → List Nat → List Nat
    | acc, [] => acc
    | acc, x :: xs => loop (insert x acc) xs
  loop [] xs

def mergeIdem (xs : List Nat) : List Nat :=
  let rec loop : Nat → List Nat → List Nat
    | curr, next :: rest =>
      if curr = next then
        loop curr rest
      else
        curr :: loop next rest
    | curr, [] => [curr]

  match xs with
  | [] => []
  | x :: xs => loop x xs

def removeNeutrals [info : ContextInformation α] (ctx : α) : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: xs =>
    match info.isNeutral ctx x with
    | true => removeNeutrals ctx xs
    | false => x :: removeNeutrals ctx xs

def norm [info : ContextInformation α] (ctx : α) (e : Expr) : List Nat :=
  let xs := e.toList
  let xs := removeNeutrals ctx xs
  let xs := if info.isComm ctx then sort xs else xs
  if info.isIdem ctx then mergeIdem xs else xs

end Lean.Meta.AC

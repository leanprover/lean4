/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/

prelude
import Init.Classical
import Init.ByCases

namespace Lean.Data.AC
inductive Expr
  | var (x : Nat)
  | op (lhs rhs : Expr)
  deriving Inhabited, Repr, BEq

open Std

structure Variable {α : Sort u} (op : α → α → α) : Type u where
  value : α
  neutral : Option $ PLift (LawfulIdentity op value)

structure Context (α : Sort u) where
  op : α → α → α
  assoc : Associative op
  comm : Option $ PLift $ Commutative op
  idem : Option $ PLift $ IdempotentOp op
  vars : List (Variable op)
  arbitrary : α

class ContextInformation (α : Sort u) where
  isNeutral : α → Nat → Bool
  isComm : α → Bool
  isIdem : α → Bool

class EvalInformation (α : Sort u) (β : Sort v) where
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

def eval (β : Sort u) [EvalInformation α β] (ctx : α) : (ex : Expr) → β
  | Expr.var idx => EvalInformation.evalVar ctx idx
  | Expr.op l r => EvalInformation.evalOp ctx (eval β ctx l) (eval β ctx r)

def Expr.toList : Expr → List Nat
  | Expr.var idx => [idx]
  | Expr.op l r => l.toList.append r.toList

def evalList (β : Sort u) [EvalInformation α β] (ctx : α) : List Nat → β
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
  | x :: xs =>
    match loop (x :: xs) with
    | [] => [x]
    | ys => ys
  | [] => []
  where loop : List Nat → List Nat
    | x :: xs =>
      match info.isNeutral ctx x with
      | true => loop xs
      | false => x :: loop xs
    | [] => []

def norm [info : ContextInformation α] (ctx : α) (e : Expr) : List Nat :=
  let xs := e.toList
  let xs := removeNeutrals ctx xs
  let xs := if info.isComm ctx then sort xs else xs
  if info.isIdem ctx then mergeIdem xs else xs

noncomputable def List.two_step_induction
  {motive : List Nat → Sort u}
  (l : List Nat)
  (empty : motive [])
  (single : ∀ a, motive [a])
  (step : ∀ a b l, motive (b :: l) → motive (a :: b :: l))
  : motive l := by
  induction l with
  | nil => assumption
  | cons a l => cases l; apply single; apply step; assumption

theorem Context.mergeIdem_nonEmpty (e : List Nat) (h : e ≠ []) : mergeIdem e ≠ [] := by
  induction e using List.two_step_induction with
  | empty => simp_all
  | single => simp [mergeIdem, mergeIdem.loop]
  | step => simp [mergeIdem, mergeIdem.loop] at *; split <;> simp_all

theorem Context.mergeIdem_head : mergeIdem (x :: x :: xs) = mergeIdem (x :: xs) := by
  simp [mergeIdem, mergeIdem.loop]

theorem Context.mergeIdem_head2 (h : x ≠ y) : mergeIdem (x :: y :: ys) = x :: mergeIdem (y :: ys) := by
  simp [mergeIdem, mergeIdem.loop, h]

theorem Context.evalList_mergeIdem (ctx : Context α) (h : ContextInformation.isIdem ctx) (e : List Nat) : evalList α ctx (mergeIdem e) = evalList α ctx e := by
  have h : IdempotentOp ctx.op := by
    simp [ContextInformation.isIdem, Option.isSome] at h;
    match h₂ : ctx.idem with
    | none =>
      simp [h₂] at h
    | some val =>
      simp [h₂] at h
      exact val.down
  induction e using List.two_step_induction with
  | empty => rfl
  | single => rfl
  | step x y ys ih =>
    cases ys with
    | nil =>
      simp [mergeIdem, mergeIdem.loop]
      split
      next h₂ => simp [evalList, h₂, h.1, EvalInformation.evalOp]
      next => rfl
    | cons z zs =>
      by_cases h₂ : x = y
      case pos =>
        rw [h₂, mergeIdem_head, ih]
        simp [evalList, ←ctx.assoc.1, h.1, EvalInformation.evalOp]
      case neg =>
        rw [mergeIdem_head2]
        by_cases h₃ : y = z
        case pos =>
          simp [mergeIdem_head, h₃, evalList]
          cases h₄ : mergeIdem (z :: zs) with
          | nil => apply absurd h₄; apply mergeIdem_nonEmpty; simp
          | cons u us => simp_all [mergeIdem, mergeIdem.loop, evalList]
        case neg =>
          simp [mergeIdem_head2, h₃, evalList] at *
          rw [ih]
        assumption

theorem insert_nonEmpty : insert x xs ≠ [] := by
  induction xs with
  | nil => simp [insert]
  | cons x xs _  => simp [insert]; split <;> simp

theorem Context.sort_loop_nonEmpty (xs : List Nat) (h : xs ≠ []) : sort.loop xs ys ≠ [] := by
  induction ys generalizing xs with
  | nil => simp [sort.loop]; assumption
  | cons y _  ih => simp [sort.loop]; apply ih; apply insert_nonEmpty

theorem Context.evalList_insert
  (ctx : Context α)
  (h : Commutative ctx.op)
  (x : Nat)
  (xs : List Nat)
  : evalList α ctx (insert x xs) = evalList α ctx (x::xs) := by
  induction xs using List.two_step_induction with
  | empty => rfl
  | single =>
    simp [insert]
    split
    . rfl
    . simp [evalList, h.1, EvalInformation.evalOp]
  | step y z zs ih =>
    simp [insert] at *; split
    next => rfl
    next =>
      split
      next => simp [evalList, EvalInformation.evalOp]; rw [h.1, ctx.assoc.1, h.1 (evalList _ _ _)]
      next => simp_all [evalList, EvalInformation.evalOp]; rw [h.1, ctx.assoc.1, h.1 (evalList _ _ _)]

theorem Context.evalList_sort_congr
  (ctx : Context α)
  (h : Commutative ctx.op)
  (h₂ : evalList α ctx a = evalList α ctx b)
  (h₃ : a ≠ [])
  (h₄ : b ≠ [])
  : evalList α ctx (sort.loop a c) = evalList α ctx (sort.loop b c) := by
  induction c generalizing a b with
  | nil => simp [sort.loop, h₂]
  | cons c _  ih =>
    simp [sort.loop]; apply ih; simp [evalList_insert ctx h, evalList]
    cases a with
    | nil => apply absurd h₃; simp
    | cons a as =>
      cases b with
      | nil => apply absurd h₄; simp
      | cons b bs => simp [evalList, h₂]
    all_goals apply insert_nonEmpty

theorem Context.evalList_sort_loop_swap
  (ctx : Context α)
  (h : Commutative ctx.op)
  (xs ys : List Nat)
  : evalList α ctx (sort.loop xs (y::ys)) = evalList α ctx (sort.loop (y::xs) ys) := by
  induction ys generalizing y xs with
  | nil => simp [sort.loop, evalList_insert ctx h]
  | cons z zs _  =>
    simp [sort.loop]; apply evalList_sort_congr ctx h
    simp [evalList_insert ctx h]
    cases h₂ : insert y xs
    . apply absurd h₂; simp [insert_nonEmpty]
    . simp [evalList, ←h₂, evalList_insert ctx h]
    all_goals simp [insert_nonEmpty]

theorem Context.evalList_sort_cons
  (ctx : Context α)
  (h : Commutative ctx.op)
  (x : Nat)
  (xs : List Nat)
  : evalList α ctx (sort (x :: xs)) = evalList α ctx (x :: sort xs) := by
  simp [sort, sort.loop]
  generalize [] = ys
  induction xs generalizing x ys with
  | nil => simp [sort.loop, evalList_insert ctx h]
  | cons z zs ih =>
    rw [evalList_sort_loop_swap ctx h]; simp [sort.loop, ←ih]; apply evalList_sort_congr ctx h; rw [evalList_insert ctx h]
    cases h₂ : insert x ys with
    | nil => apply absurd h₂; simp [insert_nonEmpty]
    | cons u us =>
      cases h₃ : insert z ys with
      | nil => apply absurd h₃; simp [insert_nonEmpty]
      | cons v vs =>
        simp [evalList, ←h₂, ←h₃, evalList_insert ctx h]
        cases ys
        . simp [evalList, h.1, EvalInformation.evalOp]
        . simp [evalList, EvalInformation.evalOp]; rw [h.1, ctx.assoc.1, h.1 (evalList _ _ _)]
    all_goals simp [insert_nonEmpty]

theorem Context.evalList_sort (ctx : Context α) (h : ContextInformation.isComm ctx) (e : List Nat) : evalList α ctx (sort e) = evalList α ctx e := by
  have h : Commutative ctx.op := by
    simp [ContextInformation.isComm, Option.isSome] at h
    match h₂ : ctx.comm with
    | none =>
      simp [h₂] at h
    | some val =>
      simp [h₂] at h
      exact val.down
  induction e using List.two_step_induction with
  | empty => rfl
  | single => rfl
  | step x y ys ih =>
    simp [evalList_sort_cons ctx h]
    cases h₂ : sort (y :: ys) with
    | nil => simp [sort, sort.loop] at *; apply absurd h₂; apply sort_loop_nonEmpty; apply insert_nonEmpty
    | cons z zs => simp [evalList, ←h₂, ih]

theorem Context.toList_nonEmpty (e : Expr) : e.toList ≠ [] := by
  induction e with
  | var => simp [Expr.toList]
  | op l r ih₁ _   =>
    simp [Expr.toList]
    cases h : l.toList with
    | nil => contradiction
    | cons => simp [List.append]

theorem Context.unwrap_isNeutral
  {ctx : Context α}
  {x : Nat}
  : ContextInformation.isNeutral ctx x = true → LawfulIdentity (EvalInformation.evalOp ctx) (EvalInformation.evalVar (β := α) ctx x) := by
  simp [ContextInformation.isNeutral, Option.isSome, EvalInformation.evalOp, EvalInformation.evalVar]
  match (var ctx x).neutral with
  | some hn =>
    intro
    exact hn.down
  | none => intro; contradiction

theorem Context.evalList_removeNeutrals (ctx : Context α) (e : List Nat) : evalList α ctx (removeNeutrals ctx e) = evalList α ctx e := by
  induction e using List.two_step_induction with
  | empty => rfl
  | single =>
    simp [removeNeutrals, removeNeutrals.loop]; split
    case h_1 => rfl
    case h_2 h => split at h <;> simp_all
  | step x y ys ih =>
    cases h₁ : ContextInformation.isNeutral ctx x <;>
    cases h₂ : ContextInformation.isNeutral ctx y <;>
    cases h₃ : removeNeutrals.loop ctx ys
    <;> simp [removeNeutrals, removeNeutrals.loop, h₁, h₂, h₃, evalList, ←ih]
    <;> (try simp [unwrap_isNeutral h₂ |>.right_id])
    <;> (try simp [unwrap_isNeutral h₁ |>.left_id])

theorem Context.evalList_append
  (ctx : Context α)
  (l r : List Nat)
  (h₁ : l ≠ [])
  (h₂ : r ≠ [])
  : evalList α ctx (l.append r) = ctx.op (evalList α ctx l) (evalList α ctx r) := by
  induction l using List.two_step_induction with
  | empty => simp_all
  | single x =>
    cases r
    . simp at h₂
    . simp [List.append, evalList, EvalInformation.evalOp]
  | step x y ys ih => simp [List.append, evalList, EvalInformation.evalOp] at *; rw [ih]; simp [ctx.assoc.1]

theorem Context.eval_toList (ctx : Context α) (e : Expr) : evalList α ctx e.toList = eval α ctx e := by
  induction e with
  | var x => rfl
  | op l r ih₁ ih₂ =>
    simp [evalList, Expr.toList, eval, ←ih₁, ←ih₂]
    apply evalList_append <;> apply toList_nonEmpty

theorem Context.eval_norm (ctx : Context α) (e : Expr) : evalList α ctx (norm ctx e) = eval α ctx e := by
  simp [norm]
  cases h₁ : ContextInformation.isIdem ctx <;> cases h₂ : ContextInformation.isComm ctx <;>
  simp_all [evalList_removeNeutrals, eval_toList, toList_nonEmpty, evalList_mergeIdem, evalList_sort]

theorem Context.eq_of_norm (ctx : Context α) (a b : Expr) (h : norm ctx a == norm ctx b) : eval α ctx a = eval α ctx b := by
  have h := congrArg (evalList α ctx) (eq_of_beq h)
  rw [eval_norm, eval_norm] at h
  assumption

end Lean.Data.AC

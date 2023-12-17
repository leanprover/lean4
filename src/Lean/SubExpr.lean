/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Daniel Selsam, Wojciech Nawrocki, E.W.Ayers
-/
import Lean.Meta.Basic
import Lean.Data.Json
import Lean.Data.RBMap

namespace Lean

/-- A position of a subexpression in an expression.

We use a simple encoding scheme for expression positions `Pos`:
every `Expr` constructor has at most 3 direct expression children. Considering an expression's type
to be one extra child as well, we can injectively map a path of `childIdxs` to a natural number
by computing the value of the 4-ary representation `1 :: childIdxs`, since n-ary representations
without leading zeros are unique. Note that `pos` is initialized to `1` (case `childIdxs == []`).

See also `SubExpr`. -/
def SubExpr.Pos := Nat

namespace SubExpr.Pos

def maxChildren := 4

/-- The coordinate `3 = maxChildren - 1` is
reserved to denote the type of the expression. -/
def typeCoord : Nat := maxChildren - 1

def asNat : Pos → Nat := id

/-- The Pos representing the root subexpression. -/
def root : Pos := (1 : Nat)

instance : Inhabited Pos := ⟨root⟩

def isRoot (p : Pos) : Bool := p.asNat < maxChildren

/-- The coordinate deepest in the Pos. -/
def head (p : Pos) : Nat :=
  if p.isRoot then panic! "already at top"
  else p.asNat % maxChildren

def tail (p : Pos) : Pos :=
  if p.isRoot then panic! "already at top"
  else (p.asNat - p.head) / maxChildren

def push (p : Pos) (c : Nat) : Pos :=
  if c >= maxChildren then panic! s!"invalid coordinate {c}"
  else p.asNat * maxChildren + c

variable {α : Type} [Inhabited α]

/-- Fold over the position starting at the root and heading to the leaf-/
partial def foldl  (f : α → Nat → α) (a : α) (p : Pos) : α :=
  if p.isRoot then a else f (foldl f a p.tail) p.head

/-- Fold over the position starting at the leaf and heading to the root-/
partial def foldr  (f : Nat → α → α) (p : Pos) (a : α) : α :=
  if p.isRoot then a else foldr f p.tail (f p.head a)

/-- monad-fold over the position starting at the root and heading to the leaf -/
partial def foldlM  [Monad M] (f : α → Nat → M α) (a : α) (p : Pos) : M α :=
  have : Inhabited (M α) := inferInstance
  if p.isRoot then pure a else do foldlM f a p.tail >>= (f · p.head)

/-- monad-fold over the position starting at the leaf and finishing at the root. -/
partial def foldrM [Monad M] (f : Nat → α → M α) (p : Pos) (a : α) : M α :=
  if p.isRoot then pure a else f p.head a >>= foldrM f p.tail

def depth (p : Pos) :=
  p.foldr (fun _ => Nat.succ) 0

/-- Returns true if `pred` is true for each coordinate in `p`.-/
def all (pred : Nat → Bool) (p : Pos) : Bool :=
  OptionT.run (m := Id) (foldrM (fun n a => if pred n then pure a else failure) p ()) |>.isSome

def append : Pos → Pos → Pos := foldl push

/-- Creates a subexpression `Pos` from an array of 'coordinates'.
Each coordinate is a number {0,1,2} expressing which child subexpression should be explored.
The first coordinate in the array corresponds to the root of the expression tree.  -/
def ofArray (ps : Array Nat) : Pos :=
  ps.foldl push root

/-- Decodes a subexpression `Pos` as a sequence of coordinates `cs : Array Nat`. See `Pos.ofArray` for details.
`cs[0]` is the coordinate for the root expression. -/
def toArray (p : Pos) : Array Nat :=
  foldl Array.push #[] p

def pushBindingDomain (p : Pos) := p.push 0
def pushBindingBody   (p : Pos) := p.push 1
def pushLetVarType    (p : Pos) := p.push 0
def pushLetValue      (p : Pos) := p.push 1
def pushLetBody       (p : Pos) := p.push 2
def pushAppFn         (p : Pos) := p.push 0
def pushAppArg        (p : Pos) := p.push 1
def pushProj          (p : Pos) := p.push 0

def pushNaryFn (numArgs : Nat) (p : Pos) : Pos :=
  p.asNat * (maxChildren ^ numArgs)

def pushNaryArg (numArgs argIdx : Nat) (p : Pos) : Pos :=
  show Nat from p.asNat * (maxChildren ^ (numArgs - argIdx)) + 1

def pushNthBindingDomain : (binderIdx : Nat) → Pos → Pos
  | 0, p => p.pushBindingDomain
  | (n+1), p => pushNthBindingDomain n p.pushBindingBody

def pushNthBindingBody : (numBinders : Nat) → Pos → Pos
  | 0, p => p
  | (n+1), p => pushNthBindingBody n p.pushBindingBody

protected def toString (p : Pos) : String :=
  p.toArray.toList
  |>.map toString
  |> String.intercalate "/"
  |> ("/" ++ ·)

open Except in
private def ofStringCoord : String → Except String Nat
  | "0" => ok 0 | "1" => ok 1 | "2" => ok 2 | "3" => ok 3
  | c => error s!"Invalid coordinate {c}"

open Except in
protected def fromString? : String → Except String Pos
  | "/" => Except.ok Pos.root
  | s =>
    match String.splitOn s "/" with
    | "" :: tail => Pos.ofArray <$> tail.toArray.mapM ofStringCoord
    | ss => error s!"malformed {ss}"

protected def fromString! (s : String) : Pos :=
  match Pos.fromString? s with
  | Except.ok a => a
  | Except.error e => panic! e

instance : Ord Pos := show Ord Nat by infer_instance
instance : DecidableEq Pos := show DecidableEq Nat by infer_instance
instance : ToString Pos := ⟨Pos.toString⟩
instance : EmptyCollection Pos := ⟨root⟩
instance : Repr Pos where
  reprPrec p _ := f!"Pos.fromString! {repr p.toString}"


-- Note: we can't send the bare Nat over the wire because Json will convert to float
-- if the nat is too big and least significant bits will be lost.
instance : ToJson Pos := ⟨toJson ∘ Pos.toString⟩
instance : FromJson Pos := ⟨fun j => fromJson? j >>= Pos.fromString?⟩

end SubExpr.Pos

/-- A subexpression of some root expression. Both its value and its position
within the root are stored. -/
structure SubExpr where
  /-- The subexpression. -/
  expr : Expr
  /-- The position of the subexpression within the root expression. -/
  pos  : SubExpr.Pos
  deriving Inhabited

namespace SubExpr

def mkRoot (e : Expr) : SubExpr := ⟨e, Pos.root⟩

/-- Returns true if the selected subexpression is the topmost one. -/
def isRoot (s : SubExpr) : Bool := s.pos.isRoot

/-- Map from subexpr positions to values. -/
abbrev PosMap (α : Type u) := RBMap Pos α compare

def bindingBody! : SubExpr → SubExpr
  | ⟨.forallE _ _ b _, p⟩ => ⟨b, p.pushBindingBody⟩
  | ⟨.lam _ _ b _, p⟩ => ⟨b, p.pushBindingBody⟩
  | _ => panic! "subexpr is not a binder"

def bindingDomain! : SubExpr → SubExpr
  | ⟨.forallE _ t _ _, p⟩ => ⟨t, p.pushBindingDomain⟩
  | ⟨.lam _ t _ _, p⟩ => ⟨t, p.pushBindingDomain⟩
  | _ => panic! "subexpr is not a binder"

instance : ToJson FVarId := ⟨fun f => toJson f.name⟩
instance : ToJson MVarId := ⟨fun f => toJson f.name⟩
instance : FromJson FVarId := ⟨fun j => FVarId.mk <$> fromJson? j⟩
instance : FromJson MVarId := ⟨fun j => MVarId.mk <$> fromJson? j⟩

/-- A location within a goal. -/
inductive GoalLocation where
  /-- One of the hypotheses. -/
  | hyp : FVarId → GoalLocation
  /-- A subexpression of the type of one of the hypotheses. -/
  | hypType : FVarId → SubExpr.Pos → GoalLocation
  /-- A subexpression of the value of one of the let-bound hypotheses. -/
  | hypValue : FVarId → SubExpr.Pos → GoalLocation
  /-- A subexpression of the goal type. -/
  | target : SubExpr.Pos → GoalLocation
  deriving FromJson, ToJson

/-- A location within a goal state. It identifies a specific goal together with a `GoalLocation`
within it. -/
structure GoalsLocation where
  /-- Which goal the location is in. -/
  mvarId : MVarId
  loc    : GoalLocation
  deriving FromJson, ToJson

end SubExpr

open SubExpr in
/-- Same as `Expr.traverseApp` but also includes a
`SubExpr.Pos` argument for tracking subexpression position. -/
def Expr.traverseAppWithPos {M} [Monad M] (visit : Pos → Expr → M Expr) (p : Pos) (e : Expr) : M Expr :=
  match e with
  | Expr.app f a =>
    e.updateApp!
      <$> traverseAppWithPos visit p.pushAppFn f
      <*> visit p.pushAppArg a
  | e => visit p e

end Lean

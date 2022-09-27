/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Meta
import Init.Data.ToString.Macro

namespace Lean

structure Position where
  line   : Nat
  column : Nat
  deriving Inhabited, DecidableEq, Repr

end Lean

open Lean

structure CallerInfo where
  module : Name
  declName? : Option Name
  position : Position

@[noinline] def CallerInfo.mkPanicMessage (info : CallerInfo) (msg : String) : String :=
  let header := match info.declName? with
    | none => "PANIC at " ++ info.module.toString
    | some declName => "PANIC at " ++ info.module.toString ++ " " ++ declName.toString
  header ++ ":" ++ toString info.position.line ++ ":" ++ toString info.position.column ++ ": " ++ msg

@[neverExtract, inline] protected def CallerInfo.panic {α : Type u} [Inhabited α] (info : CallerInfo) (msg : String) : α :=
  panic (info.mkPanicMessage msg)

macro "caller_info" : tactic => `(show CallerInfo; first | assumption | exact caller_info_here)

@[neverExtract, inline] def panicWithInfo {α : Type u} [Inhabited α]
    (msg : String) (info : CallerInfo := by caller_info) : α :=
  CallerInfo.panic info msg

@[inline] def getElem! [GetElem cont idx elem dom] [Inhabited elem]
    (xs : cont) (i : idx) [Decidable (dom xs i)] (info : CallerInfo := by caller_info) : elem :=
  if h : _ then getElem xs i h else panic! "index out of bounds"

macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)

namespace Array
variable {α : Type u}

def swap! (a : Array α) (i j : @& Nat) (info : CallerInfo := by caller_info) : Array α :=
  if h₁ : i < a.size then
  if h₂ : j < a.size then swap a ⟨i, h₁⟩ ⟨j, h₂⟩
  else panic! "index out of bounds"
  else panic! "index out of bounds"

@[inline]
def swapAt! (a : Array α) (i : Nat) (v : α) (info : CallerInfo := by caller_info) : α × Array α :=
  if h : i < a.size then
    swapAt a ⟨i, h⟩ v
  else
    have : Inhabited α := ⟨v⟩
    panic! ("index " ++ toString i ++ " out of bounds")

@[inline]
def findSome! {α : Type u} {β : Type v} [Inhabited β]
    (a : Array α) (f : α → Option β) (info : CallerInfo := by caller_info) : β :=
  match findSome? a f with
  | some b => b
  | none   => panic! "failed to find element"

/-- Insert element `a` at position `i`. Panics if `i` is not `i ≤ as.size`. -/
def insertAt! (as : Array α) (i : Nat) (a : α) (info : CallerInfo := by caller_info) : Array α :=
  if h : i ≤ as.size then
    insertAt as ⟨i, Nat.lt_succ_of_le h⟩ a
  else panic! "invalid index"

end Array

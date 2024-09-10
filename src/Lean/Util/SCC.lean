/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.HashMap
import Std.Data.HashMap.Basic
namespace Lean.SCC
/-!
  Very simple implementation of Tarjan's SCC algorithm.
  Performance is not a goal here since we use this module to
  compiler mutually recursive definitions, where each function
  (and nested let-rec) in the mutual block is a vertex.
  So, the graphs are small. -/

section
variable (α : Type) [BEq α] [Hashable α]

structure Data where
  index?   : Option Nat := none
  lowlink? : Option Nat := none
  onStack  : Bool       := false

structure State where
  stack     : List α := []
  nextIndex : Nat := 0
  data      : Std.HashMap α Data := {}
  sccs      : List (List α) := []

abbrev M := StateM (State α)
end

variable {α : Type} [BEq α] [Hashable α]

private def getDataOf (a : α) : M α Data := do
  let s ← get
  match s.data[a]? with
  | some d => pure d
  | none   => pure {}

private def push (a : α) : M α Unit :=
  modify fun s => { s with
    stack     := a :: s.stack,
    nextIndex := s.nextIndex + 1,
    data      := s.data.insert a {
      index?   := s.nextIndex,
      lowlink? := s.nextIndex,
      onStack  := true
    }
  }

private def modifyDataOf (a : α) (f : Data → Data) : M α Unit :=
  modify fun s => { s with
    data := match s.data[a]? with
      | none   => s.data
      | some d => s.data.insert a (f d)
  }

private def resetOnStack (a : α) : M α Unit :=
  modifyDataOf a fun d => { d with onStack := false }

private def updateLowLinkOf (a : α) (v : Option Nat) : M α Unit :=
  modifyDataOf a fun d => { d with
    lowlink? := match d.lowlink?, v with
      | i, none => i
      | none, i => i
      | some i, some j => if i < j then i else j
  }

private def addSCC (a : α) : M α Unit := do
  let rec add
    | [],    newSCC => modify fun s => { s with stack := [], sccs := newSCC :: s.sccs }
    | b::bs, newSCC => do
      resetOnStack b;
      let newSCC := b::newSCC;
      if a != b then
        add bs newSCC
      else
        modify fun s => { s with stack := bs, sccs := newSCC :: s.sccs }
  add (← get).stack []

private partial def sccAux (successorsOf : α → List α) (a : α) : M α Unit := do
  push a
  (successorsOf a).forM fun b => do
    let bData ← getDataOf b;
    if bData.index?.isNone then
      -- `b` has not been visited yet
      sccAux successorsOf b;
      let bData ← getDataOf b;
      updateLowLinkOf a bData.lowlink?
    else if bData.onStack then do
      -- `b` is on the stack. So, it must be in the current SCC
      -- The edge `(a, b)` is pointing to an SCC already found and must be ignored
      updateLowLinkOf a bData.index?
    else
      pure ()
  let aData ← getDataOf a;
  if aData.lowlink? == aData.index? then
    addSCC a

def scc (vertices : List α) (successorsOf : α → List α) : List (List α) :=
  let main : M α Unit := vertices.forM fun a => do
    let aData ← getDataOf a
    if aData.index?.isNone then sccAux successorsOf a
  let (_, s) := main.run {}
  s.sccs.reverse

end Lean.SCC

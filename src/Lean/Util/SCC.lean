/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.HashMap
namespace Lean
namespace SCC
/-
  Very simple implementation of Tarjan's SCC algorithm.
  Performance is not a goal here since we use this module to
  compiler mutually recursive definitions, where each function
  (and nested let-rec) in the mutual block is a vertex.
  So, the graphs are small. -/
open Std

section
variables (α : Type) [HasBeq α] [Hashable α]

structure Data :=
(index?   : Option Nat := none)
(lowlink? : Option Nat := none)
(onStack  : Bool       := false)

structure State :=
(stack     : List α := [])
(nextIndex : Nat := 0)
(data      : Std.HashMap α Data := {})
(sccs      : List (List α) := [])

abbrev M := StateM (State α)
end

variables {α : Type} [HasBeq α] [Hashable α]

private def getDataOf (a : α) : M α Data := do
s ← get;
match s.data.find? a with
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
  data := match s.data.find? a with
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

private partial def addSCCAux (a : α) : List α → List α → M α Unit
| [],    newSCC => modify fun s => { s with stack := [], sccs := newSCC :: s.sccs }
| b::bs, newSCC => do
  resetOnStack b;
  let newSCC := b::newSCC;
  if a != b then
    addSCCAux bs newSCC
  else
    modify fun s => { s with stack := bs, sccs := newSCC :: s.sccs }

private def addSCC (a : α) : M α Unit := do
s ← get;
addSCCAux a s.stack []

@[specialize] private partial def sccAux (successorsOf : α → List α) : α → M α Unit
| a => do
  push a;
  (successorsOf a).forM fun b => do {
    bData ← getDataOf b;
    if bData.index?.isNone then do
      -- `b` has not been visited yet
      sccAux b;
      bData ← getDataOf b;
      updateLowLinkOf a bData.lowlink?
    else if bData.onStack then do
      -- `b` is on the stack. So, it must be in the current SCC
      -- The edge `(a, b)` is pointing to an SCC already found and must be ignored
      updateLowLinkOf a bData.index?
    else
      pure ()
  };
  aData ← getDataOf a;
  when (aData.lowlink? == aData.index?) $
    addSCC a

@[specialize] def scc (vertices : List α) (successorsOf : α → List α) : List (List α) :=
let main : M α Unit := vertices.forM fun a => do {
  aData ← getDataOf a;
  when aData.index?.isNone do sccAux successorsOf a
};
let (_, s) := main.run {};
s.sccs.reverse

end SCC
end Lean

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Prelude
public import Init.Data.Array.QSort
public import Std.Data.HashSet
public section
namespace Lean.Meta.Grind

abbrev Var : Type := Nat
abbrev FoundVars := Std.HashSet Nat

abbrev VarCollector := FoundVars → FoundVars

def collectVar (x : Var) : VarCollector := (·.insert x)

instance : AndThen VarCollector where
  andThen c₁ c₂ := fun s => c₂ () (c₁ s)

def collectMapVars {_ : BEq α} {_ : Hashable α} (m : Std.HashMap α Expr) (k : α → VarCollector) : VarCollector := fun s => Id.run do
  let mut s := s
  for (a, _) in m do
    s := k a s
  return s

def FoundVars.toArray (s : FoundVars) : Array Var :=
  Std.HashSet.toArray s |>.qsort

structure VarRename where
  map : Std.HashMap Var Var

instance : CoeFun VarRename (fun _ => Var → Var) where
  coe := fun s x => s.map[x]?.getD 0

def mkVarRename (new2old : Array Var) : VarRename := Id.run do
  let mut old2new : Std.HashMap Var Var := {}
  let mut new := 0
  for old in new2old do
    old2new := old2new.insert old new
    new := new + 1
  { map := old2new }

end Lean.Meta.Grind

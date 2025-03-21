/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util.NumObjs

open Lean Meta

abbrev testProp := ∀ n : Nat, n = 0 + n

def thmUsingTactic : testProp := by as_aux_lemma =>
  intro n
  induction n
  · rfl
  · next ih =>
    rw [← Nat.succ_eq_add_one, Nat.add_succ, ← ih]

def thmWithoutTactic : testProp := by
  intro n
  induction n
  · rfl
  · next ih =>
    rw [← Nat.succ_eq_add_one, Nat.add_succ, ← ih]

open Lean

def size (name : Name) : MetaM Nat := do
  let env ← getEnv
  let mut totalSize : Nat := 0
  for (constantName, info) in env.constants do
    if name = constantName then
      if let some e := info.value? then
        let numObjs ← e.numObjs
        totalSize := totalSize + numObjs
  return totalSize

/--
info: as_aux_lemma makes proof term smaller : true
-/
#guard_msgs in
run_meta do
  let sizeUsingTactic ← size `thmUsingTactic
  let sizeWithoutTactic ← size `thmWithoutTactic
  logInfo m!"as_aux_lemma makes proof term smaller : {decide <| sizeUsingTactic < sizeWithoutTactic}"

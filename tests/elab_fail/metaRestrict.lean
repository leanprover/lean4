import Lean

/-!
Tests `-Dmeta.restrict=true -Dcompiler.enable=false`: no declaration of the module is compiled, so
nothing that would run the module's code works, while everything else elaborates as usual, and
restricted options cannot be changed from within the file.
-/

open Lean Elab Command

def f (x : Nat) : Nat := x + 1

theorem f_eq : f 1 = 2 := rfl

example : f 1 = 2 := by decide

structure Point where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

instance : Inhabited Point := ⟨⟨0, 0⟩⟩

initialize myRef : IO.Ref Nat ← IO.mkRef 0

/-! Code of imported modules still runs. -/

example : 2 + 2 = 4 := by simp

/-! Everything that runs code of this module fails, including the wrapper `#eval` compiles. -/

#eval f 1

#eval 1 + 1

#eval IO.println "hello"

example : f 1 = 2 := by native_decide

run_cmd logInfo "hello"

def myElab : CommandElab := fun _ => logInfo "hello"

syntax "my_cmd" : command

macro "my_term" : term => `(1)

example := my_term

notation "ℕ'" => Nat

example : ℕ' := 1

elab "my_tac" : tactic => pure ()

example : True := by my_tac; trivial

/-! Restricted options cannot be changed from within the file. -/

set_option compiler.enable true

set_option compiler.enable true in
syntax "my_cmd'" : command

set_option meta.restrict false

example : True := by
  set_option compiler.enable true in
  trivial

example : True :=
  set_option compiler.enable true in
  trivial

set_option sat.solver "/bin/false" in
example (x : BitVec 8) : x = x := by bv_decide

/-! Other options are unaffected. -/

set_option pp.all true in
example : True := trivial

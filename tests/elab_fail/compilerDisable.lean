import Lean

/-!
Tests `-Dcompiler.disable=true`: no declaration of the module is compiled, so nothing that would
run the module's code works, while everything else elaborates as usual.
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

/-! The option cannot be reset from within the file. -/

set_option compiler.disable false

syntax "my_cmd'" : command

set_option compiler.disable false in
syntax "my_cmd''" : command

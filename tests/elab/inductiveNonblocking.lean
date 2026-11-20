import Lean

/-!
Tests that `inductive` and `structure` commands do not wait for unrelated proofs that are still
being elaborated. The proofs below finish only after a signal that is sent after all the type
declarations, so they time out if any of those commands waits for them.
-/

open Lean Elab Command Tactic

run_cmd do
  let dir ← IO.FS.createTempDir
  elabCommand (← `(def $(mkIdent `signalDir) : System.FilePath := $(quote dir.toString)))

def signalFile : System.FilePath := signalDir / "signal"

elab "wait_for_signal" : tactic => do
  for _ in [0:300] do
    if ← signalFile.pathExists then return
    IO.sleep 100
  throwError "timeout: a later command waited for this proof"

/-- Like `run_cmd`, which waits for all earlier declarations in order to check for `sorry`. -/
elab "send_signal" : command => IO.FS.writeFile signalFile ""

theorem pending : True := by wait_for_signal; trivial

theorem pendingLt : 0 < 1 := by wait_for_signal; decide

def localDef : Nat := 5

abbrev LocalAbbrev := Fin localDef

inductive Enum where
  | a | b | c
  deriving DecidableEq, Repr

inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (x : α) (r : Tree α)

structure Point where
  x : Nat
  y : LocalAbbrev

structure Point3 extends Point where
  z : Enum := .a

/-! Nested occurrence in a local type, which makes the kernel generate auxiliary recursors. -/
inductive Rose where
  | mk (children : Tree Rose)

mutual
inductive Even : Nat → Prop
  | zero : Even 0
  | succ : Odd n → Even (n + 1)
inductive Odd : Nat → Prop
  | succ : Even n → Odd (n + 1)
end

/-! The signature of a pending theorem is sufficient for referring to it. -/
inductive UsesPending : Fin 1 → Type where
  | mk : UsesPending ⟨0, pendingLt⟩

class inductive Marker (α : Type) : Prop where
  | mk

send_signal

/-! Errors are still reported; a rejected declaration does wait for all earlier ones. -/
/--
error: (kernel) arg #1 of 'Bad.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Bad where
  | mk (f : Bad → Nat)

example : True := by have := @Rose.rec_1.{1}; trivial

example : Tree.leaf (α := Nat) ≠ .node .leaf 0 .leaf := nofun

example (p : Point3) : p.toPoint.x = p.x := rfl

/-- info: 'UsesPending.mk' does not depend on any axioms -/
#guard_msgs in
#print axioms UsesPending.mk

run_cmd IO.FS.removeDirAll signalDir

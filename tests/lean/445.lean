import Lean

def f : Nat → Bool
  | 0 => true
  | n + 1 => (match n with
    | 0 => true
    | _ + 1 => true) && f n

def g (i j : Nat) : Nat :=
  if i < 5 then 0 else
  match j with
  | Nat.zero => 1
  | Nat.succ j => g i j

def h (i j : Nat) : Nat :=
  i +
    match j with
    | Nat.zero => 1
    | Nat.succ j => h i j

def r (i j : Nat) : Nat :=
  i +
    match j with
    | Nat.zero => 1
    | Nat.succ j =>
      i * match j with
          | Nat.zero => 2
          | Nat.succ j => r i j

def s (i j : Nat) : Nat :=
  let z :=
    match j with
    | Nat.zero => i
    | Nat.succ j => s i j
  z + z

example : f 0 = true :=
  rfl

example : f (i+1) = ((match i with | 0 => true | _ + 1 => true) && f i) :=
  rfl

example : g i (j + 1) = if i < 5 then 0 else g i j :=
  rfl

example : g i 0 = if i < 5 then 0 else 1 :=
  rfl

example : h i 0 = i + 1 :=
  rfl

example : h i (j + 1) = i + h i j :=
  rfl

example : r i 0 = i + 1 :=
  rfl

example : r i 1 = i + i * 2 :=
  rfl

example : r i (j + 2) = i + i * r i j :=
  rfl

example : s i (j + 1) = let z := s i j; z + z :=
  rfl

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command
elab "unfold " e:term : command =>
  runTermElabM none fun xs => do
    let e ← instantiateMVars (← Term.withSynthesize <| Term.elabTerm e none)
    match (← unfoldDefinition? e) with
    | some e => logInfo m!"{e}"
    | none => throwError ""

section end

variable (i j : Nat)

unfold f 0
unfold f (i+1)
unfold g i 0
unfold g i (j+1)
unfold h i 0
unfold h i (j + 1)
unfold r i 0
unfold r i 1
unfold r i (j + 2)
unfold r i j.succ.succ
unfold s i (j + 1)

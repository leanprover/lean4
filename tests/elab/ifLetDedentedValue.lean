import Lean

/-!
Tests that `if let pat := d then t else e` parses only as `termIfLet` when a line of `d` starts left
of `let`. The `let` term ends application arguments at such a line and parses the rest as its body,
so `if (let pat := d; c) then t else e` also accepts the text. `termIfLet` must win this tie instead
of producing a choice node.
-/

open Lean Elab Command

def twoArgs (a b : Nat) : Option Nat := some (a + b)

partial def choiceKinds (stx : Syntax) : Array (Array SyntaxNodeKind) :=
  let here := if stx.isOfKind choiceKind then #[stx.getArgs.map (·.getKind)] else #[]
  stx.getArgs.foldl (init := here) fun acc arg => acc ++ choiceKinds arg

/-- Logs the alternatives of each choice node in the syntax of `cmd`, then elaborates `cmd`. -/
elab "#choices " cmd:command : command => do
  logInfo m!"{choiceKinds cmd}"
  elabCommand cmd

/-- info: [] -/
#guard_msgs in
#choices
def elseIfLet (b : Bool) (n : Nat) : Nat :=
  if b then
    1
  else if let some c :=
      twoArgs (n + 1)
        (n + 2) then
    c
  else
    2

#guard elseIfLet false 0 == 3

/-! With `;`, only the `let` condition parses. -/

/-- info: [] -/
#guard_msgs in
#choices
def letCondition (n : Nat) : Bool :=
  if let x := n + 1; x > 3 then true else false

#guard letCondition 3 && !letCondition 2

inductive Directive where
  | label (s : String)
  | instr (i : Nat)
  | byteArray (a : ByteArray)

def foo (d : Directive) :=
  match d with
  | .label _ => 0
  | .instr i => i + 1
  | .byteArray _ => 2

/--
trace: case grind
a : Nat
h : 0 = a
⊢ 0 = a
-/
#guard_msgs in
theorem ex (h : 0 = a) : foo (.label "start") = a := by
  unfold foo
  sym =>
    dsimp
    show_goals
    exact h

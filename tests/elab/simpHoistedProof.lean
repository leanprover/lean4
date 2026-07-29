opaque Bytes : Type
opaque Bytes.length : Bytes → Nat

axiom foo {α : Type} (f : α → Bytes) (len : Nat)
    (h : ∀ x, (f x).length = len) : α

def f {len : Nat} (b : { b : Bytes // b.length = len }) : Bytes :=
  b.val

noncomputable def bar (len : Nat) : { b : Bytes // b.length = len } :=
  foo f len (by simp [f])

set_option linter.tacticCheckInstances true

#guard_msgs in
example (len : Nat) : bar len = bar len := by
  unfold bar
  rfl

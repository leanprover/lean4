inductive vec (A : Sort*) : nat → Sort*
| nil  : vec 0
| cons : Π {n}, A → vec n → vec (n+1)

definition f : bool → Prop
| x :=
  let m := 10,
      n := m in
  match x with
  | tt := true
  | ff := ∀ (x : vec nat 10) (w : vec nat n), x = w
  end

set_option eqn_compiler.zeta true
definition g : bool → Prop
| x :=
  let m := 10,
      n := m in
  match x with
  | tt := true
  | ff := ∀ (x : vec nat 10) (w : vec nat n), x = w
  end

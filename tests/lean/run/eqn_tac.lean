open nat

definition foo : nat → nat
| foo zero     := begin exact zero end
| foo (succ a) := begin exact a end

example : foo zero = zero := rfl
example (a : nat) : foo (succ a) = a := rfl

definition bla : nat → nat
| bla zero := zero
| bla (succ a) :=
  begin
    apply foo,
    exact a
  end

example (a : nat) : foo (succ a) = bla (succ (succ a)) := rfl

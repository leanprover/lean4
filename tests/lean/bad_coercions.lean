open nat

constant list.{l} : Type.{l} → Type.{l}
constant vector.{l} : Type.{l} → nat → Type.{l}
constant nil (A : Type) : list A

set_option pp.coercions true
context
  parameter A : Type
  parameter n : nat

  definition foo2 [coercion] (v : vector A n) : list A :=
  nil A

  definition foo (v : vector A n) : list A :=
  nil A

  coercion foo
end

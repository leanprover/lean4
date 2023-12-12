/-!
Test that PackMutual isn't confused when a recursive call has more arguments than is packed
into the unary argument, which can happen if the return type is a function type.
-/

mutual
  inductive A : Type
  | baseA  : A
  | fromB : B → A

  inductive B : Type
  | fromA  : A → B
end

mutual
  def foo : B → Prop
  | .fromA a => bar a 0

  def bar : A → Nat → Prop
  | .baseA   => (fun _ => True)
  | .fromB b => (fun (c : Nat) => ∃ (t : Nat), foo b)
end
termination_by
  foo x => sizeOf x
  bar x => sizeOf x

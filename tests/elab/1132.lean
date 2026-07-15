class FooClass (α : Type) where
  mkFoo : {m : Type → Type} → [Monad m] → α → m Nat

inductive Baz where | a | b

instance : FooClass Baz where
  mkFoo := fun
    | .a => return 0
    | .b => return 1

instance : FooClass Baz where
  mkFoo {m} _ := fun
    | .a => return 0
    | .b => return 1

instance : FooClass Baz where
  mkFoo := fun a => match a with
    | .a => return 0
    | .b => return 1

instance : FooClass Baz where
  mkFoo := @fun
    | _, _, .a => return 1
    | _, _, .b => return 2

/-Ensure that `deriving BEq` works on structures/inductives dependently typed fields.-/

structure BVBit where
  {w : Nat}
  idx : Fin w
  foo : List (Fin w)
  bar : foo = [idx]
  deriving BEq

inductive Foo where
  | foo : (w : Nat) → Fin w → Foo
  | bar : (w : Nat) → List (Fin w) → Foo
  deriving BEq

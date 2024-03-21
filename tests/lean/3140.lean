/- Verify that `deriving BEq` works on structures with `Prop`-fields.-/

structure S where
  foo : Nat
  p : True
  Bar : Nat
  deriving BEq

#eval (⟨1,⟨⟩,2⟩ : S) == ⟨1,⟨⟩,3⟩ -- false
#eval (⟨1,⟨⟩,2⟩ : S) == ⟨2,⟨⟩,2⟩ -- false
#eval (⟨1,⟨⟩,2⟩ : S) == ⟨1,⟨⟩,2⟩ -- true

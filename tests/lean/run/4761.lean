/-!
# Make sure "anonymous dot notation" works with type synonyms.
-/

def Foo : Prop := ∀ a : Nat, a = a

protected theorem Foo.intro : Foo := sorry
example : Foo := .intro

/-!
Making sure that the type synonym `Foo'` still works.
This used to be unfolded during `forallTelescopeReducing`,
and now it is "manually" unfolded in the elaboration algorithm.
-/
example : Nat → Option Nat := .some
def Foo' := Nat → Option Nat
example : Foo' := .some

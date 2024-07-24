/-!
# Make sure "anonymous dot notation" works with type synonyms.
-/

def Foo : Prop := ∀ a : Nat, a = a

protected theorem Foo.intro : Foo := sorry
example : Foo := .intro

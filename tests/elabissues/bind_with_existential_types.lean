/-
Problem: existential types do not play well with monads.

```
class Bind (m : Type u → Type v) :=
(bind : ∀ {α β : Type u}, m α → (α → m β) → m β)
```

Even if we fix a universe-polymorphic monad M.{u v} : Type u -> Type v,
the bind operator forces the universes of the two applications of M to be the same.
So, we can not naively write:
-/

universes u v
axiom Foo : Type u → Type v
@[instance] axiom fooMonad : Monad Foo

noncomputable def doesNotWork : Foo Unit := do
x ← pure (5 : Nat);
y ← pure $ x + 3;
Z ← pure (Nat : Type);
pure ()

/- It yields the following error:

<<
bind_with_existential_types.lean:18:18: error: type mismatch at application
  pure Nat
term
  Nat
has type
  Type : Type 1
but is expected to have type
  ?m_1 : Type
>>
-/

/- We can make it work by adding a bunch of ups and downs: -/

noncomputable def moreTedious : Foo Unit := ULift.down <$> do
  x ← pure $ ULift.up (5 : Nat);
  y ← pure $ ULift.up (ULift.down x + 5);
  z ← pure (Nat : Type);
  pure $ ULift.up ()

/-
Without special elaborator support to insert all the ups and downs,
it would be highly annoying to write State monad code that uses an existential type,
e.g. a structure that simulates a Coq/ML module by bundling a type and a map API on the type.

Note that one cannot vary universes at all in generic monadic combinators,
no matter how many lifts and downlifts you are willing to perform,
since only definitions can be universe polymorphic.
If a definition takes a monad as an argument, its universe is already fixed.
-/

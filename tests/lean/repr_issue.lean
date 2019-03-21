def foo {m} [Monad m] [MonadExcept String m] [MonadState (Array Nat) m] : m Nat :=
catch (do modify $ λ a : Array Nat, a.write' 0 33,
          throw "error")
      (λ _, do a ← get, pure $ a.read' 0)

def ex₁ : StateT (Array Nat) (ExceptT String id) Nat :=
foo

def ex₂ : ExceptT String (StateT (Array Nat) id) Nat :=
foo

#exit

-- The following examples were producing an element of Type `id (Except String Nat)`.
-- Type class resolution was failing to produce an instance for `HasRepr (id (Except String Nat))` because `id` is not transparent.
#eval run ex₁ (mkArray 10 1000)
#eval run ex₂ (mkArray 10 1000)

def foo {m} [monad m] [monad_except string m] [monad_state (array nat) m] : m nat :=
catch (do modify $ λ a : array nat, a.write' 0 33,
          throw "error")
      (λ _, do a ← get, return $ a.read' 0)

def ex₁ : state_t (array nat) (except_t string id) nat :=
foo

def ex₂ : except_t string (state_t (array nat) id) nat :=
foo

-- The following examples were producing an element of type `id (except string nat)`.
-- Type class resolution was failing to produce an instance for `has_repr (id (except string nat))` because `id` is not transparent.
#eval run ex₁ (mk_array 10 1000)
#eval run ex₂ (mk_array 10 1000)

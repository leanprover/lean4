--
def foo {m} [Monad m] [MonadExcept String m] [MonadState (Array Nat) m] : m Nat :=
tryCatch
  (do modify $ fun (a : Array Nat) => a.set! 0 33;
      throw "error")
  (fun _ => do let a ← get; pure $ a.get! 0)

def ex₁ : StateT (Array Nat) (ExceptT String Id) Nat :=
foo

def ex₂ : ExceptT String (StateT (Array Nat) Id) Nat :=
foo

-- The following examples were producing an element of Type `id (Except String Nat)`.
-- Type class resolution was failing to produce an instance for `Repr (id (Except String Nat))` because `id` is not transparent.
#eval ex₁.run' (mkArray 10 1000) |>.run
#eval ex₂.run' (mkArray 10 1000) |>.run

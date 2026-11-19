namespace Exp
universe u v w

def StateT' (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

instance [Monad m] : Monad (StateT' σ m) where
  pure a := fun s => pure (a, s)

  bind x f := fun s => do
    let (a, s) ← x s
    f a s

  map f x := fun s => do
    let (a, s) ← x s
    pure (f a, s)

instance [ToString α] [ToString β] : ToString (Sum α β) where
  toString : Sum α β → String
    | Sum.inr a => "inl" ++ toString a
    | Sum.inl b => "inr" ++ toString b

end Exp

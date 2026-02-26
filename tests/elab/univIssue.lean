universe u v

@[inline] def ex1 {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α :=
  Functor.map Prod.fst (x s)

@[inline] def ex2 {σ : Type u} {m : Type u → Type v} [Functor m] {α : Type u} (x : StateT σ m α) (s : σ) : m α :=
  Prod.fst <$> x s

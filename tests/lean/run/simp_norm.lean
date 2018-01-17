universes u v

axiom map_bind_lemma : ∀ {α β : Type u} {m : Type u → Type v} [monad m] (f : α → β) (x : m α), f <$> x = x >>= pure ∘ f
attribute [norm] function.comp map_bind_lemma

example : nat.succ <$> [1, 2] = [2, 3] :=
begin
  simp with norm,
  guard_target [1, 2] >>= (λ x, pure (nat.succ x)) = [2, 3],
  simp [has_bind.bind, pure, has_pure.pure, list.ret]
end

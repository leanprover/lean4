namespace monad

class monad_transformer (transformer : ∀m [monad m], Type → Type) :=
(is_monad : ∀m [monad m], monad (transformer m))
(monad_lift : ∀m [monad m] A, m A → transformer m A)

instance transformed_monad (m t) [monad_transformer t] [monad m] : monad (t m) :=
monad_transformer.is_monad t m

class has_monad_lift (m n : Type → Type) :=
(monad_lift : ∀A, m A → n A)

instance monad_transformer_lift (t m) [monad_transformer t] [monad m] : has_monad_lift m (t m) :=
⟨monad_transformer.monad_lift t m⟩

class has_monad_lift_t (m n : Type → Type) :=
(monad_lift : ∀A, m A → n A)

def monad_lift {m n} [has_monad_lift_t m n] {A} : m A → n A :=
has_monad_lift_t.monad_lift n A

prefix `♯ `:0 := monad_lift

instance has_monad_lift_t_trans (m n o) [has_monad_lift n o] [has_monad_lift_t m n] : has_monad_lift_t m o :=
⟨ λA (ma : m A), has_monad_lift.monad_lift o A $ has_monad_lift_t.monad_lift n A ma ⟩

instance has_monad_lift_t_refl (m) [monad m] : has_monad_lift_t m m :=
⟨ λA, id ⟩

end monad

namespace state_t

def state_t_monad_lift (S) (m) [monad m] (A) (f : m A) : state_t S m A :=
take state, do res ← f, return (res, state)

instance (S) : monad.monad_transformer (state_t S) :=
⟨ state_t.monad S, state_t_monad_lift S ⟩

end state_t



universes u v

class Bind2 (m : Type u → Type v) :=
(bind : ∀ {α β : Type u}, m α → (α → m β) → m β)

set_option pp.all true

class Monad2 (m : Type u → Type v) extends Applicative m, Bind2 m : Type (max (u+1) v) :=
(map      := fun f x => Bind2.bind x (pure ∘ f))
(seq      := fun f x => Bind2.bind f fun y => Functor.map y x)
(seqLeft  := fun x y => Bind2.bind x fun a => Bind2.bind y fun _ => pure a)
(seqRight := @fun β x y => Bind2.bind x fun _ => y) -- Recall that `@` disables implicit lambda support

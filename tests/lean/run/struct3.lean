universe u v

class Bind2 (m : Type u → Type v) where
  bind : ∀ {α β : Type u}, m α → (α → m β) → m β

class Monad2 (m : Type u → Type v) : Type (max (u+1) v) extends Applicative m, Bind2 m where
  map      := fun f x => Bind2.bind x (pure ∘ f)
  seq      := fun f x => Bind2.bind f fun y => Functor.map y (x ())
  seqLeft  := fun x y => Bind2.bind x fun a => Bind2.bind (y ()) fun _ => pure a
  seqRight := @fun α β x y => Bind2.bind x fun _ => y () -- Recall that `@` disables implicit lambda support

class Monad3 (m : Type u → Type v) : Type (max (u+1) v) extends Applicative m, Bind2 m where
  map (f x)      := Bind2.bind x (pure ∘ f)
  seq (f x)      := Bind2.bind f fun y => Functor.map y (x ())
  seqLeft (x y)  := Bind2.bind x fun a => Bind2.bind (y ()) fun _ => pure a
  seqRight (x y) := Bind2.bind x fun _ => y ()

class Monad4 (m : Type u → Type v) : Type (max (u+1) v) extends Applicative m, Bind2 m where
  map f x      := Bind2.bind x (pure ∘ f)
  seq f x      := Bind2.bind f fun y => Functor.map y (x ())
  seqLeft x y  := Bind2.bind x fun a => Bind2.bind (y ()) fun _ => pure a
  seqRight x y := Bind2.bind x fun _ => y ()

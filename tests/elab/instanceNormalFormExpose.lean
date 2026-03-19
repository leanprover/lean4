class MyMonad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β

class MyLawful (m : Type → Type) [MyMonad m] where
  law : True

def MyReaderT (ρ : Type) (m : Type → Type) (α : Type) := ρ → m α
def MyStateRefT (σ : Type) (m : Type → Type) (α : Type) := MyReaderT σ m α

instance [MyMonad m] : MyMonad (MyReaderT ρ m) where
  pure a _ := MyMonad.pure a
  bind x f r := MyMonad.bind (x r) (f · r)

instance [MyMonad m] : MyMonad (MyStateRefT σ m) :=
  inferInstanceAs (MyMonad (MyReaderT _ _))

instance [MyMonad m] [MyLawful m] : MyLawful (MyReaderT ρ m) where
  law := trivial

instance [MyMonad m] [MyLawful m] : MyLawful (MyStateRefT σ m) :=
  inferInstanceAs (MyLawful (MyReaderT σ m))

instance [MyMonad m] [MyLawful m] : MyLawful (MyStateRefT σ m) :=
  inferInstanceAs (MyLawful (MyReaderT _ _))

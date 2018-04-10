class mono_monad (m : Type) (α : out_param Type) :=
(pure : α → m)
(bind : m → (α → m) → m)

export mono_monad (bind pure)

instance : mono_monad bool bool :=
{ pure := id, bind := λ b f, if b then f b else b }

#eval do b ← tt,
         b' ← ff,
         mono_monad.pure _ b

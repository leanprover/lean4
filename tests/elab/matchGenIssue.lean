example : ∀ a b c : α, a = b → b = c → a = c :=
  fun a b c h1 h2 =>
    match b, h1 with
    | _, Eq.refl a => h2

example : ∀ a b c : α, a = b → b = c → a = c :=
  fun a b c h1 h2 =>
    match h1 with
    | Eq.refl a => h2

example : ∀ a b c : α, a = b → b = c → a = c :=
  fun a b c (Eq.refl a) => fun h2 => h2

example : ∀ a b c : α, a = b → b = c → a = c :=
  fun a b c (Eq.refl a) h2 => h2

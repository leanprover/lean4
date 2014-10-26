import logic

theorem foo {A : Type} (a b c : A) : a = b → b = c → a = c :=
assume h₁ h₂, eq.trans h₁ _

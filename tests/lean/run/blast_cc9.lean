import data.list
open perm
set_option blast.strategy "cc"

example (a b : nat) : a = b → (b = a ↔ true) :=
by blast

example (a b c : nat) : a = b → b = c → (true ↔ a = c) :=
by blast

example (l₁ l₂ l₃ : list nat) : l₁ ~ l₂ → l₂ ~ l₃ → (true ↔ l₁ ~ l₃) :=
by blast

example (l₁ l₂ l₃ : list nat) : l₁ ~ l₂ → l₂ = l₃ → (true ↔ l₁ ~ l₃) :=
by blast

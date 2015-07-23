open nat

definition g : nat → nat → nat :=
sorry

definition R : nat → nat → Prop :=
sorry

lemma C₁ [congr] : g 0 1 = g 1 0 :=  -- ERROR
sorry

lemma C₂ [congr] (a b : nat) : g a b = 0 := -- ERROR
sorry

lemma C₃ [congr] (a b : nat) : R (g a b) (g 0 0) := -- ERROR
sorry

lemma C₄ [congr] (A B : Type) : (A → B) = (λ a : nat, B → A) 0 := -- ERROR
sorry

lemma C₅ [congr] (A B : Type₁) : (A → nat) = (B → nat) := -- ERROR
sorry

lemma C₆ [congr] (A B : Type₁) : A = B := -- ERROR
sorry

lemma C₇ [congr] (a b c d : nat) : (∀ (x : nat), x > c → a = c) → g a b = g c d := -- ERROR
sorry

lemma C₈ [congr] (a b c d : nat) : (c = a) → g a b = g c d := -- ERROR
sorry

lemma C₉ [congr] (a b c d : nat) : (a = c) → (b = c) → g a b = g c d := -- ERROR
sorry

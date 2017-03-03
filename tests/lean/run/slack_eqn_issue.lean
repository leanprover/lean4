lemma test1 {p : ℕ → Prop} {a : ℕ} (h : p a) : ∀b, b = a → p b
| ._ rfl := h

lemma test2 {p : ℕ → Prop} {a : ℕ} (h : p a) : ∀b, b = a → p a
| ._ rfl := h

lemma test3 {p : ℕ → Prop} {a : ℕ} (h : p a) : ∀b, a = b → p b
| ._ rfl := h

lemma test4 {p : ℕ → Prop} {a : ℕ} {f : ℕ → ℕ} (h : p (f a)) : ∀b, b = f a → p b
| ._ rfl := h

lemma test5 {p : ℕ → Prop} {a : ℕ} {f : ℕ → ℕ} (h : p (f a)) : ∀b, f a = b → p b
| ._ rfl := h

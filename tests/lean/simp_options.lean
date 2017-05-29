lemma simp_rule :
    forall (A B C : Type)
           (xs : list A)
           (f: A → B)
           (g: B → C), (list.map g $ (list.map f) xs) = list.map (g ∘ f) xs :=
begin
    intros,
    induction xs,
    simp [list.map],
    simp [list.map],
end

lemma simp_wildcard :
forall (A B C : Type)
(a b : list A)
(a' b' : list C)
(f : A → B)
(g h : B → C),
(list.map g $ list.map f a) = a' ->
(list.map h $ list.map f b) = b' ->
a' = list.map (g ∘ f) a ∧ b' = list.map (h ∘ f) b :=
begin
    intros A B C a b a' b' f g h a₁ a₂,
    simp [simp_rule] at *,
    rw [a₁, a₂],
    split; reflexivity
end

constants (f : ℕ → ℕ) (a b c : ℕ) (fab : f a = f b) (fbc : f b = f c)
constants (p : ℕ → Prop) (pfa : p (f a)) (pfb : p (f b)) (pfc :p (f c))

attribute [simp] fbc

example : p (f a) :=
by simp [fab]; exact pfc

example : p (f a) :=
by simp only [fab]; exact pfb

example (h : p (f a)) : p (f c) :=
by simp [fab] at h; assumption

example (h : p (f a)) : p (f b) :=
by simp only [fab] at h; assumption

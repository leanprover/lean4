def Top := ∀ p : Prop, p → p
def PExt := ∀ (A B : Prop), A → B → A = B
def supercast (h : PExt) (A B : Prop) (a : A) (b : B) : B
  := @cast A B (h A B a b) a
def omega : PExt → Top :=
  λ h A a => supercast h (Top → Top) A
    (λ z: Top => z (Top → Top) (λ x => x) z) a
def Omega : PExt → Top :=
  λ h => omega h (Top → Top) (λ x => x) (omega h)
def Omega' : PExt → Top := λ h => (λ p x => x)

theorem loopy : Omega = Omega' := rfl

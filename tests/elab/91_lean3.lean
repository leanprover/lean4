def top := ∀ p : Prop, p → p
def pext := ∀ (A B : Prop), A → B → A = B
def supercast (h : pext) (A B : Prop) (a : A) (b : B) : B
  := @cast A B (h A B a b) a
def omega : pext → top :=
  λ h A a => supercast h (top → top) A
    (λ z: top => z (top → top) (λ x => x) z) a
def Omega : pext → top :=
  λ h => omega h (top → top) (λ x => x) (omega h)
def Omega' : pext → top := λ h => (λ p x => x)

theorem loopy : Omega = Omega' := rfl

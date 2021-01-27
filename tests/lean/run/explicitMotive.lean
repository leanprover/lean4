
def f1 (ex : Empty) {α : Type} : α :=
Empty.rec (motive := fun _ => α) ex

def f2 (a b : Nat) (h₁ : b = a) (h₂ : a + b = b) : a + a = b :=
Eq.rec (motive := fun x _ => a + x = b) h₂ h₁

def f3 (a b : Nat) (h₁ : b = a) (h₂ : a + b = b) : a + a = b :=
Eq.recOn (motive := fun x _ => a + x = b) h₁ h₂

def tautext {A B : Prop} (a : A) (b : B)
: A = B := propext (Iff.intro (λ _ => b) (λ _ => a))
def True' : Prop := ∀ A : Prop, A → A
def delta : True' → True' := λ z : True' => z (True' → True') id z
def omega : True' := λ _ a => cast (tautext id a) delta
def Omega : True' := delta omega

def tt : True := Omega _ .intro

def f (h : True ∧ True) : Nat := And.rec (motive := fun _ => Nat) (fun _ _ => 1) h

example : f (Omega _ ⟨.intro,.intro⟩) = 1 := rfl

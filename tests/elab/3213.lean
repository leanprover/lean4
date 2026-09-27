
section
variable (P Q : Prop) (A : Type) (f : P → Q → A) (x : P ∧ Q)

example : And.rec f ⟨x.1,x.2⟩ = f (And.left x) (And.right x) := rfl
-- `x` needs to get eta-expanded for this to pass
example : (And.rec f ⟨x.1,x.2⟩ : A) = And.rec f x := rfl
end

set_option linter.defProp false

def tautext {A B : Prop} (a : A) (b : B)
: A = B := propext (Iff.intro (λ _ => b) (λ _ => a))
def True' : Prop := ∀ A : Prop, A → A
def delta : True' → True' := λ z : True' => z (True' → True') id z
def omega : True' := λ _ a => cast (tautext id a) delta
def Omega : True' := delta omega

def tt : True := Omega _ .intro

def f (h : True ∧ True) : Nat := And.rec (motive := fun _ => Nat) (fun _ _ => 1) h

-- Ensures `(Omega _ ⟨.intro,.intro⟩)` gets eta-expanded *before* getting reduced, ensuring the term never actually evaluates
example : f (Omega _ ⟨.intro,.intro⟩) = 1 := rfl

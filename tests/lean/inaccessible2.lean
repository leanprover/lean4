set_option new_elaborator true

inductive imf {A B : Type*} (f : A → B) : B → Type
| mk : ∀ (a : A), imf (f a)

definition inv_1 {A B : Type*} (f : A → B) : ∀ (b : B), imf f b → A
| .(f .a) (imf.mk .f a)  := a  -- Error inaccessible annotation inside inaccessible annotation

definition inv_2 {A B : Type*} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) (let x := (imf.mk .f a) in x)  := a  -- Error invalid occurrence of 'let' expression

definition inv_3 {A B : Type*} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) ((λ (x : imf f b), x) (imf.mk .f a)) := a  -- Error invalid occurrence of 'lambda' expression

definition symm {A : Type*} : ∀ a b : A, a = b → b = a
| .a .a (eq.refl a) := rfl -- Error `a` in eq.refl must be marked as inaccessible since it is an inductive datatype parameter

inductive imf {A B : Sort*} (f : A → B) : B → Sort*
| mk : ∀ (a : A), imf (f a)

definition inv_1 {A B : Sort*} (f : A → B) : ∀ (b : B), imf f b → A
| .(f .(a)) (imf.mk .(f) a)  := a  -- Error inaccessible annotation inside inaccessible annotation

definition inv_2 {A B : Sort*} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) (let x := (imf.mk .(f) a) in x)  := a  -- Error invalid occurrence of 'let' expression

definition inv_3 {A B : Sort*} (f : A → B) : ∀ (b : B), imf f b → A
| .(f a) ((λ (x : imf f b), x) (imf.mk .(f) a)) := a  -- Error invalid occurrence of 'lambda' expression

definition sym {A : Sort*} : ∀ a b : A, a = b → b = a
| .(a) .(a) (eq.refl a) := rfl -- Error `a` in eq.refl must be marked as inaccessible since it is an inductive datatype parameter

definition symm2 {A : Sort*} : ∀ a b : A, a = b → b = a
| _ _ rfl := rfl -- correct version

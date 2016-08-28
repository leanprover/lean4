set_option new_elaborator true

inductive imf {A B : Type} (f : A → B) : B → Type
| mk : ∀ (a : A), imf (f a)

definition inv_1 {A B : Type} (f : A → B) : ∀ (b : B), imf f b → A
| .(f .a) (imf.mk .f a)  := a  -- Error inaccessible annotation inside inaccessible annotation

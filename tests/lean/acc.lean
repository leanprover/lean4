namespace play
inductive acc (A : Type) (R : A → A → Prop) :  A → Prop
| intro : ∀ (x : A), (∀ (y : A), R y x → acc y) → acc x

check @acc.rec
end play

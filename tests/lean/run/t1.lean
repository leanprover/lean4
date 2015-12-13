prelude
definition Prop : Type.{1} := Type.{0}
print raw ((Prop))
print raw Prop
print raw fun (x y : Prop), x x
print raw fun (x y : Prop) {z : Prop}, x y
print raw λ [x : Prop] [y : Prop] {z : Prop}, x z
print raw Pi (x y : Prop) {z : Prop}, x
print raw ∀ (x y : Prop) {z : Prop}, x
print raw forall {x y : Prop} w {z : Prop}, x

set_option pp.implicit true
set_option pp.notation false

definition symm : Π {A : Type} {a b : A}, a = b → b = a,
symm rfl := rfl

definition trans : Π {A : Type} {a b c : A}, a = b → b = c → a = c,
trans rfl rfl := rfl

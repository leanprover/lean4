set_option pp.implicit true
set_option pp.notation false

definition symm {A : Type} : Π {a b : A}, a = b → b = a,
symm rfl := rfl

definition trans {A : Type} : Π {a b c : A}, a = b → b = c → a = c,
trans rfl rfl := rfl

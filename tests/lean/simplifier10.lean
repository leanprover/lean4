import logic.connectives logic.quantifiers

universe l
constants (T : Type.{l}) (x y z : T) (P : T → Prop) (Q : T → T → T → Prop) (R W V : T → T → Prop)
constants (px : P x) (wxz : W x z) (vzy : V z y)
constants (H : ∀ (x y z : T), P x → W x z → V z y → (Q z y x ↔ R x y))

attribute px true_iff [simp]
attribute wxz [simp]
attribute vzy [simp]
attribute H [simp]

#simplify iff env 0 P x
#simplify iff env 0 W x z
#simplify iff env 0 V z y
#simplify iff env 0 Q z y x
#simplify iff env 0 V z y ↔ Q z y x

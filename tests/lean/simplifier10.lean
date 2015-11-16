import logic.connectives logic.quantifiers

universe l
constants (T : Type.{l}) (x y z : T) (P : T → Prop) (Q : T → T → T → Prop) (R W V : T → T → Prop)
constants (px : P x) (wxz : W x z) (vzy : V z y)
constants (H : ∀ (x y z : T), P x → W x z → V z y → (Q z y x ↔ R x y))
namespace tst
attribute px true_iff [simp]
attribute wxz [simp]
attribute vzy [simp]
attribute H [simp]
end tst

#simplify iff tst 0 P x
#simplify iff tst 0 W x z
#simplify iff tst 0 V z y
#simplify iff tst 0 Q z y x
#simplify iff tst 0 V z y ↔ Q z y x

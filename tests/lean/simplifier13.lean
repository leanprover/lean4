universe l
constants (T : Type.{l}) (f : T →  T → T) (g : T → T)
constants (P : T → Prop) (Q : Prop) (Hfg : ∀ (x : T), f x x = g x)
constants (c : Π (x y z : T), P x → P y → P z → Q)
constants (x y z : T) (px : P (f x x)) (py : P (f y y)) (pz : P (g z))
namespace tst
attribute Hfg [simp]
end tst
-- TODO(Daniel): extra step? Similar to simplifier1.hlean
#simplify eq tst 0 c (f x x) (f y y) (g z) px py pz

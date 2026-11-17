import Std.Tactic.BVDecide

/-
x * (y * z) = (x * y) * z
-/

example {α : Type} (i a b c : α) (product : α → α → α → Prop)
    (hleft_id : ∀ x, product i x x)
    (hright_id : ∀ x, product x i x)
    (hsquare : ∀ x, product x x i)
    (hassoc1 : ∀ x y z u v w, ¬(product x y u) ∨ ¬(product y z v) ∨ ¬(product u z w) ∨ product x v w)
    (hassoc2 : ∀ x y z u v w, ¬(product x y u) ∨ ¬(product y z v) ∨ ¬(product x v w) ∨ product u z w)
    (h1 : product a b c)
    (h2 : ¬product b a c) : False := by
  bv_decide (cegarRounds := 135) (eprSymBreak := .simple) +epr +uf


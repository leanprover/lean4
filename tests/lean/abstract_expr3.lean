universes l1 l2
constants (X : Type.{l1}) (P : X → Type.{l2}) (P_ss : ∀ x, subsingleton (P x))
constants (x1 x2 : X) (px1a px1b : P x1) (px2a px2b : P x2)
attribute P_ss [instance]
constants (f : Π (x1 x2 : X), P x1 → P x2 → Prop)

#abstract_expr 0 f
#abstract_expr 0 f x1
#abstract_expr 0 f x1 x2
#abstract_expr 0 f x1 x2 px1a
#abstract_expr 0 f x1 x2 px1b
#abstract_expr 0 f x1 x2 px1a px2a
#abstract_expr 0 f x1 x2 px1a px2b

#abstract_expr 1 f x1 x2, f x2 x1
#abstract_expr 1 f x1 x2, f x1 x2 px1a
#abstract_expr 1 f x1 x2 px1a, f x1 x2 px1b
#abstract_expr 1 f x1 x2 px1a px2a, f x1 x2 px1b
#abstract_expr 1 f x1 x2 px1a px2a, f x1 x2 px1b px2b

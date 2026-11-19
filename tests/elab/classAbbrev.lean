class Refl.{U} {α : Type U} (R : α → α → Prop) : Prop where
  refl (a : α) : R a a

class Symm.{U} {α : Type U} (R : α → α → Prop) : Prop where
  symm {a b : α} : R a b → R b a

/--
  An example decl modifier (a doc comment).
-/
class abbrev PEquiv.{U} {α : Type U} (R : α → α → Prop) : Prop 
  := Refl R, Symm R

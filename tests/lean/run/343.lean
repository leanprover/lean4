set_option pp.mvars false

structure CatIsh where
  Obj : Type o
  Hom : Obj → Obj → Type m

infixr:75 " ~> " => (CatIsh.Hom _)

structure FunctorIsh (C D : CatIsh) where
  onObj : C.Obj → D.Obj
  onHom : ∀ {s d : C.Obj}, (s ~> d) → (onObj s ~> onObj d)

abbrev Catish : CatIsh :=
  {
    Obj := CatIsh
    Hom := FunctorIsh
  }

universe m o
unif_hint (mvar : CatIsh) where
  Catish.{m, o} =?= mvar |- mvar.Obj =?= CatIsh.{o, m}

structure CtxSyntaxLayerParamsObj where
  Ct : CatIsh

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def CtxSyntaxLayerParams : CatIsh :=
  {
    Obj := CtxSyntaxLayerParamsObj
    Hom := sorry
  }

/--
error: stuck at solving universe constraint
  max (_+1) (_+1) =?= max (_+1) (_+1)
while trying to unify
  CatIsh.Obj.{max (max (_ + 1) (_ + 1)) _ _, max ((max (_ + 1) (_ + 1)) + 1) ((max _ _) + 1)}
    Catish.{max (_ + 1) (_ + 1), max _ _} : Type (max ((max (_ + 1) (_ + 1)) + 1) ((max _ _) + 1))
with
  CatIsh.{max _ _, max (_ + 1) (_ + 1)} : Type (max ((max _ _) + 1) ((max (_ + 1) (_ + 1)) + 1))
---
error: failed to solve universe constraint
  max (_+1) (_+1) =?= max (_+1) (_+1)
while trying to unify
  Catish.Obj : Type (max ((max (u_1 + 1) (u_2 + 1)) + 1) ((max u_3 u_4) + 1))
with
  CatIsh : Type (max ((max u_4 u_3) + 1) ((max (u_4 + 1) (u_3 + 1)) + 1))
-/
#guard_msgs in
def CtxSyntaxLayerTy := CtxSyntaxLayerParams ~> Catish

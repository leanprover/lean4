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
  Catish.{m, o} =?= mvar |- mvar.Obj =?= CatIsh.{m,o}

structure CtxSyntaxLayerParamsObj where
  Ct : CatIsh

def CtxSyntaxLayerParams : CatIsh :=
  {
    Obj := CtxSyntaxLayerParamsObj
    Hom := sorry
  }

def CtxSyntaxLayerTy := CtxSyntaxLayerParams ~> Catish

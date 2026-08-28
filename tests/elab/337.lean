section
  variable (G : Type 1) (T : Type 1)
           (EG : G → G → Type)
           (getCtx : T → G)
  inductive CtxSyntaxLayer where
  inductive TySyntaxLayer where
  | arrow : {Γ : G} → (A B : T) → EG Γ (getCtx A) → EG Γ (getCtx B) → TySyntaxLayer
end
section
  variable (G : Type 1) (T : Type 1) (Tm : Type 1)
           (EG : G → G → Type) (ET : T → T → Type)
           (getCtx : T → G) (getTy : Tm → T)
           (TAlgebra : TySyntaxLayer G T EG getCtx → T)

  inductive TmSyntaxLayer where
    | app : {Γ : G} → (A B : T) → (Actx : EG Γ (getCtx A)) → (Bctx : EG Γ (getCtx B))
        → (f x : Tm)
        → ET (getTy f) (TAlgebra (TySyntaxLayer.arrow A B Actx Bctx))
        → ET (getTy x) A
        → TmSyntaxLayer
end

structure Ty where
  ctx : Type
  ty : ctx → Type
structure Tm where
  ty : Ty
  tm : ∀ {Γ}, ty.ty Γ

def ECtx : Type → Type → Type := (PLift $ · = ·)
def ETy  : Ty  → Ty  → Type := (PLift $ · = ·)
def ETm  : Tm  → Tm  → Type := (PLift $ · = ·)

def interpTyStep : TySyntaxLayer Type Ty ECtx Ty.ctx → Ty
  | TySyntaxLayer.arrow (Γ:=Γ) A B (PLift.up Actx) (PLift.up Bctx) => Ty.mk Γ (λ γ => A.ty (cast Actx γ) → B.ty (cast Bctx γ))

def interpTmStep : TmSyntaxLayer Type Ty Tm ECtx ETy Ty.ctx Tm.ty interpTyStep → Tm
  | TmSyntaxLayer.app (Γ:=Γ1) A B (PLift.up Actx) (PLift.up Bctx) { ty := fty , tm := ftm } x (PLift.up fTy) (PLift.up xTy)
    => sorry

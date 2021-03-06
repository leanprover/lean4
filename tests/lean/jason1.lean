section
  variable (G : Type) (T : Type) (Tm : Type)
           (EG : G → G → Type) (ET : T → T → Type) (ETm : Tm → Tm → Type)
           (getCtx : T → G) (getTy : Tm → T)
  inductive CtxSyntaxLayer where
    | emp : CtxSyntaxLayer
    | snoc : (Γ : G) → (t : T) → EG Γ (getCtx t) → CtxSyntaxLayer
end
section
  variable (G : Type) (T : Type) (Tm : Type)
           (EG : G → G → Type) (ET : T → T → Type) (ETm : Tm → Tm → Type)
           (getCtx : T → G) (getTy : Tm → T)
-- : CtxSyntaxLayer G T EG getCtx → G)

  inductive TySyntaxLayer where
  | top : {Γ : G} → TySyntaxLayer
  | bot : {Γ : G} → TySyntaxLayer
  | nat : {Γ : G} → TySyntaxLayer
  | arrow : {Γ : G} → (A B : T) → EG Γ (getCtx A) → EG Γ (getCtx B) → TySyntaxLayer

  def getCtxStep : TySyntaxLayer G T EG getCtx → G
    | TySyntaxLayer.top (Γ := Γ) .. => Γ
    | TySyntaxLayer.bot (Γ := Γ) .. => Γ
    | TySyntaxLayer.nat (Γ := Γ) .. => Γ
    | TySyntaxLayer.arrow (Γ := Γ) .. => Γ
end
section
  variable (G : Type) (T : Type) (Tm : Type)
           (EG : G → G → Type) (ET : T → T → Type) (ETm : Tm → Tm → Type)
           (EGrfl : ∀ {Γ}, EG Γ Γ)
           (getCtx : T → G) (getTy : Tm → T)
           (GAlgebra : CtxSyntaxLayer G T EG getCtx → G) (TAlgebra : TySyntaxLayer G T EG getCtx → T)

  inductive TmSyntaxLayer where
    | tt : {Γ : G} → TmSyntaxLayer
    | zero : {Γ : G} → TmSyntaxLayer
    | succ : {Γ : G} → TmSyntaxLayer
    | app : {Γ : G} → (A B : T) → (Actx : EG Γ (getCtx A)) → (Bctx : EG Γ (getCtx B))
        → (f x : Tm)
        → ET (TAlgebra (TySyntaxLayer.arrow A B Actx Bctx)) (getTy f)
        → ET A (getTy x)
        → TmSyntaxLayer

  set_option pp.all true
  def getTyStep : TmSyntaxLayer G T Tm EG ET getCtx getTy TAlgebra → T
    | TmSyntaxLayer.tt ..   => TAlgebra TySyntaxLayer.top
    | TmSyntaxLayer.zero .. => TAlgebra TySyntaxLayer.nat
    | TmSyntaxLayer.succ .. => TAlgebra (TySyntaxLayer.arrow (TAlgebra TySyntaxLayer.nat) (TAlgebra TySyntaxLayer.nat) EGrfl EGrfl)
    | TmSyntaxLayer.app (B:=B) .. => B
end

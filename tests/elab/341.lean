section
  variable (G : Type 1) (T : Type 1) (Tm : Type 1)
           (EG : G → G → Type) (ET : T → T → Type) (ETm : Tm → Tm → Type)
           (getCtx : T → G) (getTy : Tm → T)
  inductive CtxSyntaxLayer where
    | emp : CtxSyntaxLayer
    | snoc : (Γ : G) → (t : T) → EG Γ (getCtx t) → CtxSyntaxLayer
end
section
  variable (G : Type 1) (T : Type 1) (Tm : Type 1)
           (EG : G → G → Type) (ET : T → T → Type) (ETm : Tm → Tm → Type)
           (getCtx : T → G) (getTy : Tm → T)
           (GAlgebra : CtxSyntaxLayer G T EG getCtx → G)

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
  variable (G : Type 1) (T : Type 1) (Tm : Type 1)
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
        → ET (getTy f) (TAlgebra (TySyntaxLayer.arrow A B Actx Bctx))
        → ET (getTy x) A
        → TmSyntaxLayer
  -- set options for debugging "(kernel) declaration has metavariables" errors
  --set_option trace.Elab.definition true
  --set_option pp.explicit true
  def getTyStep : TmSyntaxLayer G T Tm EG ET getCtx getTy TAlgebra → T
    | TmSyntaxLayer.tt (Γ:=Γ) .. => TAlgebra (TySyntaxLayer.top (Γ:=Γ))
    | TmSyntaxLayer.zero (Γ:=Γ) .. => TAlgebra (TySyntaxLayer.nat (Γ:=Γ))
    | TmSyntaxLayer.succ (Γ:=Γ) .. => TAlgebra (TySyntaxLayer.arrow (TAlgebra (TySyntaxLayer.nat (Γ:=Γ))) (TAlgebra (TySyntaxLayer.nat (Γ:=Γ))) EGrfl EGrfl)
    | TmSyntaxLayer.app (B:=B) .. => B
end

structure SyntaxModel where
  Ctx : Type 1
  Ty : Type 1
  Tm : Type 1
  EC : Ctx → Ctx → Type
  ETy : Ty → Ty → Type
  ETm : Tm → Tm → Type
  getCtx : Ty → Ctx
  getTy : Tm → Ty
  interpCStep : CtxSyntaxLayer Ctx Ty EC getCtx → Ctx
  interpTyStep : TySyntaxLayer Ctx Ty EC getCtx → Ty
  interpTmStep : TmSyntaxLayer Ctx Ty Tm EC ETy getCtx getTy interpTyStep → Tm

namespace SetModel
  def Ctx := Type
  structure Ty where
    ctx : Ctx
    ty : ctx → Type
  structure Tm where
    ty : Ty
    tm : ∀ {Γ}, ty.ty Γ

  def ECtx : Ctx → Ctx → Type := (PLift $ · = ·)
  def ETy  : Ty  → Ty  → Type := (PLift $ · = ·)
  def ETm  : Tm  → Tm  → Type := (PLift $ · = ·)

  def interpCStep : CtxSyntaxLayer Ctx Ty ECtx Ty.ctx → Ctx
    | CtxSyntaxLayer.emp => Unit
    | CtxSyntaxLayer.snoc _ T (PLift.up rfl) => Σ γ : _, T.ty γ

  def Ty.inj Γ T := Ty.mk Γ (λ _ => T)
  def Ty.Unit {Γ} := Ty.inj Γ _root_.Unit
  def Ty.Empty {Γ} := Ty.inj Γ _root_.Empty
  def Ty.Nat {Γ} := Ty.inj Γ _root_.Nat

  def Tm.inj Γ {T} (t : T) := Tm.mk (Ty.inj Γ T) t

  def interpTyStep : TySyntaxLayer Ctx Ty ECtx Ty.ctx → Ty
    | TySyntaxLayer.top (Γ:=Γ) => Ty.Unit (Γ:=Γ)
    | TySyntaxLayer.bot (Γ:=Γ) => Ty.Empty (Γ:=Γ)
    | TySyntaxLayer.nat (Γ:=Γ) => Ty.Nat (Γ:=Γ)
    | TySyntaxLayer.arrow (Γ:=Γ) A B (PLift.up Actx) (PLift.up Bctx) => Ty.mk Γ (λ γ => A.ty (cast Actx γ) → B.ty (cast Bctx γ))

  def interpTmStep : TmSyntaxLayer Ctx Ty Tm ECtx ETy Ty.ctx Tm.ty interpTyStep → Tm
    | TmSyntaxLayer.tt (Γ:=Γ) => Tm.inj Γ Unit.unit
    | TmSyntaxLayer.zero (Γ:=Γ) => Tm.inj Γ (0 : Nat)
    | TmSyntaxLayer.succ (Γ:=Γ) => Tm.inj Γ Nat.succ
    | TmSyntaxLayer.app (Γ:=Γ) A B (PLift.up Actx) (PLift.up Bctx) (Tm.mk fty ftm) (Tm.mk (Ty.mk xctx xty) xtm) (PLift.up fTy) (PLift.up xTy)
        => { ty := B
           , tm := fun {γ} =>
                     (by
                       simp at fTy xTy; subst fTy xTy; simp at Actx Bctx; subst Actx Bctx
                       exact (ftm xtm)
                     )
               }

  def Model : SyntaxModel :=
    {
      Ctx := Ctx
    , Ty := Ty
    , Tm := Tm
    , EC := ECtx
    , ETy := ETy
    , ETm := ETm
    , getCtx := Ty.ctx
    , getTy := Tm.ty
    , interpCStep := interpCStep
    , interpTyStep := interpTyStep
    , interpTmStep := interpTmStep
    }
end SetModel

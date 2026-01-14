structure RingHom (R₁ R₂ : Type) where
  toFun : R₁ → R₂

def RingHom.comp {R₁ R₂ R₃ : Type} (σ' : RingHom R₂ R₃) (σ : RingHom R₁ R₂)  : RingHom R₁ R₃ where
  toFun := σ'.toFun ∘ σ.toFun

def RingHom.id (R : Type) : RingHom R R where
  toFun := _root_.id

structure RingHomInvPair {R₁ R₂ : Type} (σ : RingHom R₁ R₂) (σ' : RingHom R₂ R₁) : Prop where
  comp_eq : σ'.comp σ = RingHom.id R₁
  comp_eq₂ : σ.comp σ' = RingHom.id R₂

structure LinearEquiv (R : Type) (σ : RingHom R R) (invPair : RingHomInvPair σ σ)

structure AffineEquiv (k P₁ P₂ : Type) (V₁ V₂ : Type) where
  toFun : P₁ → P₂
  linear : LinearEquiv k (RingHom.id k) ⟨rfl, rfl⟩

variable {k P₁ P₂ V₁ V₂ : Type}

def toAffineMap {k P₁ P₂ V₁ V₂ : Type} (e : AffineEquiv k P₁ P₂ V₁ V₂) : P₁ → P₂ :=
  e.toFun


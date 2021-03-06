constant foo : {x : Nat} → Type
constant bar : {T : Type} → ({x : T} → Type) → Type
structure Baz where
  baz : {x : Nat} → Type

#check bar foo
#check fun (b : Baz) => bar b.baz


structure Ty where
  ctx : Type
  ty : ctx → Type
structure Tm where
  ty : Ty
  tm : ∀ {Γ}, ty.ty Γ

#check fun (Γ : Type)
(A : Ty)
(Actx : Γ = A.ctx)
(x : Tm)
(xTy : x.ty = A)
=> Eq.rec (motive := fun ty _ => ∀ {Γ:ty.ctx}, ty.ty Γ) (fun {Γ} => x.tm (Γ:=Γ)) xTy

#check fun (Γ : Type)
(A : Ty)
(Actx : Γ = A.ctx)
(x : Tm)
(xTy : x.ty = A)
=> Eq.rec (motive := fun ty _ => ∀ {Γ:ty.ctx}, ty.ty Γ) x.tm xTy

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
=> Eq.rec (motive := fun ty _ => ∀ {Γ}, ty.ty Γ) (fun {Γ:x.ty.ctx} => x.tm (Γ:=Γ)) xTy

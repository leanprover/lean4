set_option pp.mvars false

opaque foo : {x : Nat} → Type
opaque bar : {T : Type} → ({x : T} → Type) → Type
structure Baz where
  baz : {x : Nat} → Type

/-- info: bar fun {x} => foo : Type -/
#guard_msgs in
#check bar foo

/-- info: fun b => bar fun {x} => b.baz : Baz → Type -/
#guard_msgs in
#check fun (b : Baz) => bar b.baz


structure Ty where
  ctx : Type
  ty : ctx → Type
structure Tm where
  ty : Ty
  tm : ∀ {Γ}, ty.ty Γ

/--
info: fun Γ A x x_1 xTy =>
  Eq.rec (motive := fun ty x => {Γ : ty.ctx} → ty.ty Γ) (fun {Γ} => x_1.tm)
    xTy : (Γ : Type) → (A : Ty) → (x : Γ = A.ctx) → (x_1 : Tm) → (xTy : x_1.ty = A) → A.ty (?_ Γ A x x_1 xTy)
-/
#guard_msgs in
#check fun (Γ : Type)
(A : Ty)
(_ : Γ = A.ctx)
(x : Tm)
(xTy : x.ty = A)
=> Eq.rec (motive := fun ty _ => ∀ {Γ:ty.ctx}, ty.ty Γ) (fun {Γ} => x.tm (Γ:=Γ)) xTy

/--
info: fun Γ A x x_1 xTy =>
  Eq.rec (motive := fun ty x => {Γ : ty.ctx} → ty.ty Γ) (fun {Γ} => x_1.tm)
    xTy : (Γ : Type) → (A : Ty) → (x : Γ = A.ctx) → (x_1 : Tm) → (xTy : x_1.ty = A) → A.ty (?_ Γ A x x_1 xTy)
-/
#guard_msgs in
#check fun (Γ : Type)
(A : Ty)
(_ : Γ = A.ctx)
(x : Tm)
(xTy : x.ty = A)
=> Eq.rec (motive := fun ty _ => ∀ {Γ:ty.ctx}, ty.ty Γ) x.tm xTy

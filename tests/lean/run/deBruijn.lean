inductive HList {α : Type u} (β : α → Type u) : List α → Type u
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons

inductive Member : α → List α → Type _
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
  | a::as, .head => a
  | a::as, .tail h => as.get h

inductive Ty where
  | nat
  | fn : Ty → Ty → Ty

abbrev Ty.denote : Ty → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote

inductive Term : List Ty → Ty → Type
  | var   : Member ty ctx → Term ctx ty
  | const : Nat → Term ctx .nat
  | plus  : Term ctx .nat → Term ctx .nat → Term ctx .nat
  | app   : Term ctx (.fn dom ran) → Term ctx dom → Term ctx ran
  | lam   : Term (dom :: ctx) ran → Term ctx (.fn dom ran)
  | «let» : Term ctx ty₁ → Term (ty₁ :: ctx) ty₂ → Term ctx ty₂

def Term.denote : Term ctx ty → HList Ty.denote ctx → ty.denote
  | var h,     env => env.get h
  | const n,   _   => n
  | plus a b,  env => a.denote env + b.denote env
  | app f a,   env => f.denote env (a.denote env)
  | lam b,     env => fun x => b.denote (x :: env)
  | «let» a b, env => b.denote (a.denote env :: env)

def Term.constFold : Term ctx ty → Term ctx ty
  | const n   => const n
  | var h     => var h
  | app f a   => app f.constFold a.constFold
  | lam b     => lam b.constFold
  | «let» a b => «let» a.constFold b.constFold
  | plus a b  =>
    match a.constFold, b.constFold with
    | const n, const m => const (n+m)
    | a',      b'      => plus a' b'

theorem Term.constFold_sound (e : Term ctx ty) : e.constFold.denote env = e.denote env := by
  induction e with
  | const => rfl
  | var => rfl
  | app f a ihf iha => simp [constFold]; rw [denote, denote, iha, ihf]
  | lam b ih => simp [constFold]; rw [denote, denote]; simp [ih]
  | «let» a b iha ihb => simp [constFold]; rw [denote, denote, iha, ihb]
  | plus a b iha ihb =>
    simp [constFold]
    split
    next he₁ he₂ => rw [denote, denote, ← iha, ← ihb, he₁, he₂, denote, denote]
    next he₁ he₂ _ _ _ => rw [denote, denote, ← he₁, ← he₂, iha, ihb]

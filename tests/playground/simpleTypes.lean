import Lean

opaque Erased : Type
opaque Any : Type
notation "◾" => Erased
notation "⊤" => Any

open Lean Meta

def erasedExpr := mkConst ``Erased
def anyExpr := mkConst  ``Any

partial def simpType (type : Expr) : MetaM Expr := do
  if (← isProp type) then
    return erasedExpr
  let type ← whnf type
  match type with
  | .sort u     => return .sort u
  | .const ..   => visitApp type #[]
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      let borrowed := isMarkedBorrowed d
      let mut d ← simpType d
      if borrowed then
        d := markBorrowed d
      let b ← simpType (b.instantiate1 x)
      return .forallE n d (b.abstract #[x]) bi
  | .app ..  => type.withApp visitApp
  | .fvar .. => visitApp type #[]
  | _        => return anyExpr
where
  visitApp (f : Expr) (args : Array Expr) := do
    let fNew ← match f with
      | .const declName us =>
        let .inductInfo _ ← getConstInfo declName | return anyExpr
        pure <| .const declName us
      | .fvar .. => pure f
      | _ => return anyExpr
    let mut result := fNew
    for arg in args do
      if (← isProp arg) then
        result := mkApp result erasedExpr
      else if (← isTypeFormer arg) then
        result := mkApp result (← simpType arg)
      else
        result := mkApp result erasedExpr
    return result

def test (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let type ← simpType info.type
  IO.println s!"{declName} : {← ppExpr type}"

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def Vec.zip : Vec α n → Vec β n → Vec (α × β) n
  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)
  | .nil, .nil => .nil

def Tuple (α : Type u) : Nat → Type u
  | 0   => PUnit
  | 1   => α
  | n+2 => α × Tuple α n

def mkConstTuple (a : α) : (n : Nat) → Tuple α n
  | 0   => ⟨⟩
  | 1   => a
  | n+2 => (a, mkConstTuple a n)

#eval test ``Vec.zip
#eval test ``mkConstTuple
#eval test ``Fin.add
#eval test ``Vec.cons
#eval test ``Eq.rec
#eval test ``GetElem.getElem

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons

inductive Member : α → List α → Type _
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
  | a::as, .head => a
  | _::as, .tail h => as.get h

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

#eval test ``Term.constFold
#eval test ``Term.denote
#eval test ``HList.get
#eval test ``Member.head
#eval test ``Ty.denote
#eval test ``MonadControl.liftWith
#eval test ``MonadControl.restoreM
#eval test ``Decidable.casesOn
#eval test ``getConstInfo
#eval test ``instMonadMetaM
#eval test ``inferType
#eval test ``Elab.Term.elabTerm
#eval test ``Nat.add

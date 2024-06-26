import Lean

open Lean Compiler LCNF Meta

def test (declName : Name) : MetaM Unit := do
  IO.println s!"{declName} : {← ppExpr (← LCNF.getOtherDeclBaseType declName [])}"

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
#eval test ``Lean.Meta.inferType
#eval test ``Elab.Term.elabTerm
#eval test ``Nat.add

structure Magma where
  carrier : Type
  mul : carrier → carrier → carrier

#eval test ``Magma.mul

def weird1 (c : Bool) : (cond c List Array) Nat :=
  match c with
  | true => []
  | false => #[]

#eval test ``weird1

axiom monadList₁.{u} : Monad List.{u}
axiom monadList₂.{u} : Monad (fun α : Type u => List α)

axiom lamAny₁ (c : Bool) : Monad (fun α : Type => cond c (List α) (Array α))
axiom lamAny₂ (c : Bool) : Monad (cond c List.{0} Array.{0})
#eval test ``lamAny₁
#eval test ``lamAny₂

def testMono (declName : Name) : MetaM Unit := do
  let base ← LCNF.getOtherDeclBaseType declName []
  let mono ← LCNF.toMonoType base
  IO.println s!"{declName} : {← ppExpr mono}"

set_option pp.explicit true
#eval testMono ``Term.constFold
#eval testMono ``Term.denote
#eval testMono ``HList.get
#eval testMono ``Member.head
#eval testMono ``Ty.denote
#eval testMono ``MonadControl.liftWith
#eval testMono ``MonadControl.restoreM
#eval testMono ``Decidable.casesOn
#eval testMono ``getConstInfo
#eval testMono ``instMonadMetaM
#eval testMono ``Lean.Meta.inferType
#eval testMono ``Elab.Term.elabTerm
#eval testMono ``Nat.add
#eval testMono ``Fin.add
#eval testMono ``HashSetBucket.update

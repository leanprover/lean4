import Lean

def HList (αs : List (Type u)) : Type u := αs.foldr Prod.{u, u} PUnit

@[match_pattern] def HList.nil : HList [] := ⟨⟩
@[match_pattern] def HList.cons (a : α) (as : HList αs): HList (α :: αs) := (a, as)

def HList.set {αs : List (Type u)} (as : HList αs) (i : Fin αs.length) (v : αs.get i) : HList αs :=
  match αs, as, i, v with
  | _ :: _, cons _ as, ⟨0,          _⟩, b => cons b as
  | _ :: _, cons a as, ⟨Nat.succ n, h⟩, b => cons a (set as ⟨n, Nat.le_of_succ_le_succ h⟩ b)
  | [],     nil,       _,               _ => nil

open Lean.Compiler
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option trace.Compiler.result true
#eval compile #[``HList.set]

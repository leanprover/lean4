namespace Ex

class GetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  getElem' (xs : Cont) (i : Idx) : Elem

export GetElem (getElem')

instance : GetElem Lean.Syntax Nat Lean.Syntax where
  getElem' xs i := xs.getArg i

instance : GetElem (Array α) Nat α where
  getElem' xs i := xs.get i sorry

open Lean

def f (stx : Option Syntax) : Syntax :=
  stx.getD default

def bad (doFor : Syntax) : Syntax :=
  let doForDecls := (getElem' doFor 1).getArgs
  let doForDecl := getElem' doForDecls 1
  f (getElem' doForDecl 1)

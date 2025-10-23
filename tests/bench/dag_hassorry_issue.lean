import Lean

open Lean

def mkEqX (bidx : Nat) : Expr :=
  mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Nat []) (.bvar bidx) (.bvar bidx)

def mkReflX (bidx : Nat) : Expr :=
  mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Nat []) (.bvar bidx)

def mkAnds (n : Nat) : Expr :=
  match n with
  | 0 => mkConst ``True []
  | n+1 => mkAnd (mkEqX n) (mkAnds n)

def mkAndIntro (p q h₁ h₂ : Expr) : Expr :=
  mkApp4 (mkConst ``And.intro []) p q h₁ h₂

def mkRefls (n : Nat) (ands : List Expr) : Expr :=
  match n, ands with
  | n+1, and::ands => mkAndIntro (mkEqX n) and (mkReflX n) (mkRefls n ands)
  | _, _ => mkConst ``True.intro []

def mkLambdas (n : Nat) (p : Expr) : Expr :=
  match n with
  | 0 => p
  | n+1 => .lam `x (mkConst ``Nat []) (mkLambdas n p) .default

def mkForalls (n : Nat) (p : Expr) : Expr :=
  match n with
  | 0 => p
  | n+1 => .forallE `x (mkConst ``Nat []) (mkForalls n p) .default

partial def toAndList (ands : Expr) (acc : List Expr) : List Expr :=
  if ands.isAppOf ``And then
    toAndList (ands.getArg! 1) (ands.getArg! 1 :: acc)
  else
    (ands :: acc).reverse

def test (n : Nat) : CoreM Unit := do
  let and := mkAnds n
  let type := mkForalls n and
  let andList := toAndList and []
  let value := mkLambdas n (mkRefls n andList)
  addDecl <| .thmDecl {
    name := (`test_abst).appendIndexAfter n
    levelParams := []
    type, value
  }
  return ()

def main (args : List String) : IO Unit := do
  let [size] := args | throw (IO.userError s!"unexpected number of arguments, numeral expected")
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init.Prelude }] {} 0
  discard <| test size.toNat! |>.toIO { fileName := "<test>", fileMap := default } { env }
  IO.println "ok"

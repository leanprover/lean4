import Lean.Meta

open Lean
open Lean.Meta

unsafe def tstInferType (mods : List Name) (e : Expr) : IO Unit :=
withImportModules (mods.map $ fun m => {module := m}) {} 0 fun env => do
   let (type, _, _) ← (inferType e : MetaM _).toIO {} { env := env } {} {};
   IO.println (toString e ++ " : " ++ toString type)

unsafe def tstWHNF (mods : List Name) (e : Expr) (t := TransparencyMode.default) : IO Unit :=
withImportModules (mods.map $ fun m => {module := m}) {} 0 fun env => do
   let (s, _, _) ← (whnf e : MetaM _).toIO {} { env := env };
   IO.println (toString e ++ " ==> " ++ toString s)

unsafe def tstIsProp (mods : List Name) (e : Expr) : IO Unit :=
withImportModules (mods.map $ fun m => {module := m}) {} 0 fun env => do
  let (b, _, _) ← (isProp e : MetaM _).toIO {} { env := env };
  IO.println (toString e ++ ", isProp: " ++ toString b)

def t1 : Expr :=
let map  := mkConst `List.map [levelOne, levelOne];
let nat  := mkConst `Nat [];
let bool := mkConst `Bool [];
mkAppN map #[nat, bool]

#eval tstInferType [`Init.Data.List] t1

def t2 : Expr :=
let prop := mkSort levelZero;
mkForall `x BinderInfo.default prop prop

#eval tstInferType [`Init.Core] t2

def t3 : Expr :=
let nat   := mkConst `Nat [];
let natLe := mkConst `Nat.le [];
let zero  := mkLit (Literal.natVal 0);
let p     := mkAppN natLe #[mkBVar 0, zero];
mkForall `x BinderInfo.default nat p

#eval tstInferType [`Init.Data.Nat] t3

def t4 : Expr :=
let nat   := mkConst `Nat [];
let p     := mkAppN (mkConst `Nat.succ []) #[mkBVar 0];
mkLambda `x BinderInfo.default nat p

#eval tstInferType [`Init.Core] t4

def t5 : Expr :=
let add   := mkConst `Nat.add [];
mkAppN add #[mkLit (Literal.natVal 3), mkLit (Literal.natVal 5)]

#eval tstWHNF [`Init.Data.Nat] t5
#eval tstWHNF [`Init.Data.Nat] t5 TransparencyMode.reducible

set_option pp.all true
#check @List.cons Nat

def t6 : Expr :=
let map  := mkConst `List.map [levelOne, levelOne];
let nat  := mkConst `Nat [];
let add  := mkConst `Nat.add [];
let f    := mkLambda `x BinderInfo.default nat (mkAppN add #[mkBVar 0, mkLit (Literal.natVal 1)]);
let cons := mkApp (mkConst `List.cons [levelZero]) nat;
let nil  := mkApp (mkConst `List.nil [levelZero]) nat;
let one  := mkLit (Literal.natVal 1);
let four := mkLit (Literal.natVal 4);
let xs   := mkApp (mkApp cons one) (mkApp (mkApp cons four) nil);
mkAppN map #[nat, nat, f, xs]

#eval tstInferType [`Init.Data.List] t6
#eval tstWHNF [`Init.Data.List] t6

#eval tstInferType [] $ mkSort levelZero

#eval tstInferType [`Init.Data.List] $ mkLambda `a BinderInfo.implicit (mkSort levelOne) (mkLambda `x BinderInfo.default (mkBVar 0) (mkLambda `xs BinderInfo.default (mkApp (mkConst `List [levelZero]) (mkBVar 1)) (mkBVar 0)))

def t7 : Expr :=
let nat  := mkConst `Nat [];
let one  := mkLit (Literal.natVal 1);
mkLet `x nat one one

#eval tstInferType [`Init.Core] $ t7
#eval tstWHNF [`Init.Core] $ t7

def t8 : Expr :=
let nat  := mkConst `Nat [];
let one  := mkLit (Literal.natVal 1);
let add  := mkConst `Nat.add [];
mkLet `x nat one (mkAppN add #[one, mkBVar 0])

#eval tstInferType [`Init.Core] $ t8
#eval tstWHNF [`Init.Core] $ t8

def t9 : Expr :=
let nat  := mkConst `Nat [];
mkLet `a (mkSort levelOne) nat (mkForall `x BinderInfo.default (mkBVar 0) (mkBVar 1))

#eval tstInferType [`Init.Core] $ t9
#eval tstWHNF [`Init.Core] $ t9

#eval tstInferType [`Init.Core] $ mkLit (Literal.natVal 10)
#eval tstInferType [`Init.Core] $ mkLit (Literal.strVal "hello")
#eval tstInferType [`Init.Core] $ mkMData {} $ mkLit (Literal.natVal 10)

def t10 : Expr :=
let nat  := mkConst `Nat [];
let refl := mkApp (mkConst `Eq.refl [levelOne]) nat;
mkLambda `a BinderInfo.default nat (mkApp refl (mkBVar 0))

#eval tstInferType [`Init.Core] t10
#eval tstIsProp [`Init.Core] t10

#eval tstIsProp [`Init.Core] (mkAppN (mkConst `And []) #[mkConst `True [], mkConst `True []])

#eval tstIsProp [`Init.Core] (mkConst `And [])

-- Example where isPropQuick fails
#eval tstIsProp [`Init.Core] (mkAppN (mkConst `id [levelZero]) #[mkSort levelZero, mkAppN (mkConst `And []) #[mkConst `True [], mkConst
 `True []]])

#eval tstIsProp [`Init.Core] (mkAppN (mkConst `Eq [levelOne]) #[mkConst `Nat [], mkLit (Literal.natVal 0), mkLit (Literal.natVal 1)])

#eval tstIsProp [`Init.Core] $
  mkForall `x BinderInfo.default (mkConst `Nat [])
    (mkAppN (mkConst `Eq [levelOne]) #[mkConst `Nat [], mkBVar 0, mkLit (Literal.natVal 1)])

#eval tstIsProp [`Init.Core] $
  mkApp
    (mkLambda `x BinderInfo.default (mkConst `Nat [])
      (mkAppN (mkConst `Eq [levelOne]) #[mkConst `Nat [], mkBVar 0, mkLit (Literal.natVal 1)]))
    (mkLit (Literal.natVal 0))

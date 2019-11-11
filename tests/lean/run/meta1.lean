import Init.Lean.Meta
open Lean
open Lean.Meta

def tstInferType (mods : List Name) (e : Expr) : IO Unit :=
do env ← importModules mods;
   match inferType e {} { env := env } with
   | EStateM.Result.ok type s   => IO.println (toString e ++ " : " ++ toString type)
   | EStateM.Result.error err _ => throw (IO.userError (toString err))

def tstWHNF (mods : List Name) (e : Expr) : IO Unit :=
do env ← importModules mods;
   match whnf e {} { env := env } with
   | EStateM.Result.ok type s   => IO.println (toString e ++ " ==> " ++ toString type)
   | EStateM.Result.error err _ => throw (IO.userError (toString err))

def t1 : Expr :=
let map  := Expr.const `List.map [Level.one, Level.one];
let nat  := Expr.const `Nat [];
let bool := Expr.const `Bool [];
mkApp map #[nat, bool]

#eval tstInferType [`Init.Data.List] t1

def t2 : Expr :=
let prop := Expr.sort Level.zero;
Expr.forallE `x BinderInfo.default prop prop

#eval tstInferType [`Init.Core] t2

def t3 : Expr :=
let nat   := Expr.const `Nat [];
let natLe := Expr.const `Nat.le [];
let zero  := Expr.lit (Literal.natVal 0);
let p     := mkApp natLe #[Expr.bvar 0, zero];
Expr.forallE `x BinderInfo.default nat p

#eval tstInferType [`Init.Data.Nat] t3

def t4 : Expr :=
let nat   := Expr.const `Nat [];
let p     := mkApp (Expr.const `Nat.succ []) #[Expr.bvar 0];
Expr.lam `x BinderInfo.default nat p

#eval tstInferType [`Init.Core] t4

def t5 : Expr :=
let add   := Expr.const `Nat.add [];
mkApp add #[Expr.lit (Literal.natVal 3), Expr.lit (Literal.natVal 5)]

#eval tstWHNF [`Init.Data.Nat] t5

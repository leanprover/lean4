import Init.Lean.Meta
open Lean
open Lean.Meta

def tstInferType (mods : List Name) (e : Expr) : IO Unit :=
do env ← importModules mods;
   match inferType e {} { env := env } with
   | EStateM.Result.ok type s   => IO.println (toString e ++ " : " ++ toString type)
   | EStateM.Result.error err _ => throw (IO.userError (toString err))

def tstWHNF (mods : List Name) (e : Expr) (t := TransparencyMode.default) : IO Unit :=
do env ← importModules mods;
   match whnf e { config := { transparency := t } } { env := env } with
   | EStateM.Result.ok type s   => IO.println (toString e ++ " ==> " ++ toString type)
   | EStateM.Result.error err _ => throw (IO.userError (toString err))

def tstIsProp (mods : List Name) (e : Expr) : IO Unit :=
do env ← importModules mods;
   match isProp e {} { env := env } with
   | EStateM.Result.ok b s      => IO.println (toString e ++ ", isProp: " ++ toString b)
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
#eval tstWHNF [`Init.Data.Nat] t5 TransparencyMode.reducible

set_option pp.all true
#check @List.cons Nat

def t6 : Expr :=
let map  := Expr.const `List.map [Level.one, Level.one];
let nat  := Expr.const `Nat [];
let add  := Expr.const `Nat.add [];
let f    := Expr.lam `x BinderInfo.default nat (mkApp add #[Expr.bvar 0, Expr.lit (Literal.natVal 1)]);
let cons := Expr.app (Expr.const `List.cons [Level.zero]) nat;
let nil  := Expr.app (Expr.const `List.nil [Level.zero]) nat;
let one  := Expr.lit (Literal.natVal 1);
let four := Expr.lit (Literal.natVal 4);
let xs   := Expr.app (Expr.app cons one) (Expr.app (Expr.app cons four) nil);
mkApp map #[nat, nat, f, xs]

#eval tstInferType [`Init.Data.List] t6
#eval tstWHNF [`Init.Data.List] t6

#eval tstInferType [] $ Expr.sort Level.zero

#eval tstInferType [`Init.Data.List] $ Expr.lam `a BinderInfo.implicit (Expr.sort Level.one) (Expr.lam `x BinderInfo.default (Expr.bvar 0) (Expr.lam `xs BinderInfo.default (Expr.app (Expr.const `List [Level.zero]) (Expr.bvar 1)) (Expr.bvar 0)))

def t7 : Expr :=
let nat  := Expr.const `Nat [];
let one  := Expr.lit (Literal.natVal 1);
Expr.letE `x nat one one

#eval tstInferType [`Init.Core] $ t7
#eval tstWHNF [`Init.Core] $ t7

def t8 : Expr :=
let nat  := Expr.const `Nat [];
let one  := Expr.lit (Literal.natVal 1);
let add  := Expr.const `Nat.add [];
Expr.letE `x nat one (mkApp add #[one, Expr.bvar 0])

#eval tstInferType [`Init.Core] $ t8
#eval tstWHNF [`Init.Core] $ t8

def t9 : Expr :=
let nat  := Expr.const `Nat [];
Expr.letE `a (Expr.sort Level.one) nat (Expr.forallE `x BinderInfo.default (Expr.bvar 0) (Expr.bvar 1))

#eval tstInferType [`Init.Core] $ t9
#eval tstWHNF [`Init.Core] $ t9

#eval tstInferType [`Init.Core] $ Expr.lit (Literal.natVal 10)
#eval tstInferType [`Init.Core] $ Expr.lit (Literal.strVal "hello")
#eval tstInferType [`Init.Core] $ Expr.mdata {} $ Expr.lit (Literal.natVal 10)

#eval tstInferType [`Init.Lean.Trace] (Expr.proj `Inhabited 0 (Expr.const `Lean.TraceState.Inhabited []))
#eval tstInferType [`Init.Lean.Trace] (Expr.proj `Lean.TraceState 0 (Expr.proj `Inhabited 0 (Expr.const `Lean.TraceState.Inhabited [])))
#eval tstWHNF [`Init.Lean.Trace] (Expr.proj `Inhabited 0 (Expr.const `Lean.TraceState.Inhabited []))
#eval tstWHNF [`Init.Lean.Trace] (Expr.proj `Lean.TraceState 0 (Expr.proj `Inhabited 0 (Expr.const `Lean.TraceState.Inhabited [])))

def t10 : Expr :=
let nat  := Expr.const `Nat [];
let refl := Expr.app (Expr.const `Eq.refl [Level.one]) nat;
Expr.lam `a BinderInfo.default nat (Expr.app refl (Expr.bvar 0))

#eval tstInferType [`Init.Core] t10
#eval tstIsProp [`Init.Core] t10

#eval tstIsProp [`Init.Core] (mkApp (Expr.const `And []) #[Expr.const `True [], Expr.const `True []])

#eval tstIsProp [`Init.Core] (Expr.const `And [])

-- Example where isPropQuick fails
#eval tstIsProp [`Init.Core] (mkApp (Expr.const `id [Level.zero]) #[Expr.sort Level.zero, mkApp (Expr.const `And []) #[Expr.const `True [], Expr.const
 `True []]])

#eval tstIsProp [`Init.Core] (mkApp (Expr.const `Eq [Level.one]) #[Expr.const `Nat [], Expr.lit (Literal.natVal 0), Expr.lit (Literal.natVal 1)])

#eval tstIsProp [`Init.Core] $
  Expr.forallE `x BinderInfo.default (Expr.const `Nat [])
    (mkApp (Expr.const `Eq [Level.one]) #[Expr.const `Nat [], Expr.bvar 0, Expr.lit (Literal.natVal 1)])

#eval tstIsProp [`Init.Core] $
  Expr.app
    (Expr.lam `x BinderInfo.default (Expr.const `Nat [])
      (mkApp (Expr.const `Eq [Level.one]) #[Expr.const `Nat [], Expr.bvar 0, Expr.lit (Literal.natVal 1)]))
    (Expr.lit (Literal.natVal 0))

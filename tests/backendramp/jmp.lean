--  lean %s 2>&1 1>/dev/null | hask-opt  | FileCheck %s
--  RUN: ./run-lean.sh %s | FileCheck %s --check-prefix=CHECK-INTERPRET
--  RUN: ./validate-lean.sh %s 
--  run: lean %s 2>&1 1>/dev/null | hask-opt  --lz-interpret="mode=lambdapure" | FileCheck %s --check-prefix=CHECK-INTERPRET

-- Testcase to check a join point / jump instruction

-- CHECK: "lz.jump"
-- CHECK: "lz.block"
-- CHECK: func @main

set_option trace.compiler.ir.init true


-- We've arranged for the output to be 0, 1, 2

-- CHECK-INTERPRET:      0  
-- CHECK-INTERPRET-NEXT: 1
-- CHECK-INTERPRET-NEXT: 2


inductive Expr
| Add : Expr -> Expr -> Expr
| Foo : Nat -> Expr
| Val : Nat -> Expr

namespace Expr
open Nat

def eval : Expr -> Expr
 | Add _ (Val _) => Val 0
 | Add (Val _) e => Val 1
 |  x            => Val 2


-- def eval (e: Expr) -> Expr
-- case e of
--   Add x y -> 
--      case y of
--         Val -> Val 0
--         _ -> case x of
--                 Val -> Val 1
--                 Foo _ -> Val 2 -- repeated case
--                 Add _ _ -> Val 2 -- repeated case
--    _ -> Val 2 -- repeated case
--   Foo _ -> Val 2 -- REPEAT
--   Val _ -> Val 2 -- REPEAT
--  

--  | Add e (Val b) => Val 0
--  | Add (Val b) e => Val 1
--  |  x            => Val 2
-- 

def toNat : Expr -> Nat
 | Val v => v
 | _ => 420
 	
end Expr
open Expr
-- | Check output to be 0, 1, 2

unsafe def main (xs: List String) : IO Unit := do
  IO.println (toString (toNat (eval (Add (Foo 1) (Val 2)))));
  IO.println (toString (toNat (eval (Add (Val 1) (Foo 2)))));
  IO.println (toString (toNat (eval (Add (Foo 1) (Foo 2)))));


-- def Expr.eval (arg : obj) : obj :=
-- | case arg : obj of
-- | Expr.Add → // arg = Add ...
-- |   let l : obj := proj[0] arg;
-- |   let r : obj := proj[1] arg;
-- |   JUMPBB (### : obj) :=  // CHECKS FOR (ADD ? VAL)
-- |   | case r : obj of Add ? ?
-- |   | Expr.Add → Add ? (Add ? ?)
-- |   | | let cl1 : obj := Expr.eval._closed_1; // 2
-- |   | | ret cl1
-- |   | Expr.Foo → // Add ? Foo
-- |   | | let cl1 : obj := Expr.eval._closed_1; // 2
-- |   | | ret cl1
-- |   | Expr.Val → // Add ? Val
-- |   | | let cl2 : obj := Expr.eval._closed_2; // 0
-- |   | | ret cl2;
-- |   case l : obj of  Add l ?
-- |   Expr.Add → // Add (Add ? ?)
-- |   | let x_5 : obj := ctor_0[PUnit.unit];
-- |   | jmp JUMPBB x_5 // Add (Add ? ?) => JUMP
-- |   Expr.Foo → // Add Foo ?
-- |   | let x_6 : obj := ctor_0[PUnit.unit];
-- |   | jmp JUMPBB x_6  // Add Foo ? => JUMP
-- |   Expr.Val → // Add Val ?
-- |   | case r : obj of
-- |   | Expr.Add → // Add Val (Add ? ?)
-- |   | | let cl3 : obj := Expr.eval._closed_3; // 1
-- |   | | ret cl3
-- |   | Expr.Foo → // Add Val Foo
-- |   | | let cl3 : obj := Expr.eval._closed_3; // 1
-- |   | | ret cl3
-- |   | Expr.Val → // Add Val Val
-- |   | | let cl2 : obj := Expr.eval._closed_2; // 0
-- |   | | ret cl2
-- | Expr.Foo → // Foo 
-- | | let cl1 : obj := Expr.eval._closed_1; // 2
-- | | ret cl1
-- | Expr.Val → // Val 
-- | | let cl1 : obj := Expr.eval._closed_1; // 2
-- | | ret cl1

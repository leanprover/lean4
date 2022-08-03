open Std
-- set_option trace.compiler.ir.init true


inductive A where
| a1 : A
| a2 : A
| a3 : A
| a4 : A
deriving Inhabited
open A


partial def A.toString (a: A): Int := 
 match a with
 | a1 => 42
 | a2 => 42
 | a3 => 42
 | a4 => 43

partial def A.fromString (x: String): A := 
  match x with
  | "a1" => A.a1
  | "a2" => A.a2
  | "a3" => A.a3
  | "a4" => A.a4
  | _ => A.a1


def main (xs: List String): IO Unit := do
  match xs with
  | (s::_) => IO.println (A.fromString s).toString
  | _ => IO.println A.a2.toString

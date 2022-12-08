import Lean

namespace Foo
def f (x y : Nat) := x + y + x
scoped infix:65 " ++ " => f
end Foo

open Foo in
def f1 (x : Nat) := x ++ x

#print f1

def f2 (x : Nat) := open Foo in x ++ x

#print f2

open Foo in
#print f1

open Lean.Parser.Command in
def syntaxMatcher : Unit :=
  match Lean.Syntax.missing with
    | `(declId|$id:ident$[.{$ls,*}]?) => () -- unknown parser declId
    | _                               => ()

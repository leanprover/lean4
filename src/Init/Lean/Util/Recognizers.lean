/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr

namespace Lean
namespace Expr

@[inline] def app1? (e : Expr) (fName : Name) : Option Expr :=
if e.isAppOfArity fName 1 then
  some $ e.appArg!
else
  none

@[inline] def app2? (e : Expr) (fName : Name) : Option (Expr × Expr) :=
if e.isAppOfArity fName 2 then
  some $ (e.appFn!.appArg!, e.appArg!)
else
  none

@[inline] def app3? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr) :=
if e.isAppOfArity fName 3 then
  some $ (e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
else
  none

@[inline] def app4? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr) :=
if e.isAppOfArity fName 4 then
  some $ (e.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
else
  none

@[inline] def eq? (p : Expr) : Option (Expr × Expr × Expr) :=
p.app3? `Eq

@[inline] def iff? (p : Expr) : Option (Expr × Expr) :=
p.app2? `Iff

@[inline] def heq? (p : Expr) : Option (Expr × Expr × Expr × Expr) :=
p.app4? `HEq

@[inline] def arrow? : Expr → Option (Expr × Expr)
| Expr.forallE _ α β _ => if β.hasLooseBVars then none else some (α, β)
| _                    => none

partial def listLitAux : Expr → List Expr → Option (List Expr)
| e, acc =>
  if e.isAppOfArity `List.nil 1 then
    some acc.reverse
  else if e.isAppOfArity `List.cons 3 then
    listLitAux e.appArg! (e.appFn!.appArg! :: acc)
  else
    none

def listLit? (e : Expr) : Option (List Expr) :=
listLitAux e []

def arrayLit? (e : Expr) : Option (List Expr) :=
match e.app2? `List.toArray with
| some (_, e) => e.listLit?
| none        => none

/-- Recognize `α × β` -/
def prod? (e : Expr) : Option (Expr × Expr) :=
e.app2? `Prod

end Expr
end Lean

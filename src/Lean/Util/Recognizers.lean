/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean
namespace Expr

@[inline] def const? (e : Expr) : Option (Name × List Level) :=
  match e with
  | Expr.const n us => some (n, us)
  | _ => none

@[inline] def app1? (e : Expr) (fName : Name) : Option Expr :=
  if e.isAppOfArity fName 1 then
    some e.appArg!
  else
    none

@[inline] def app2? (e : Expr) (fName : Name) : Option (Expr × Expr) :=
  if e.isAppOfArity fName 2 then
    some (e.appFn!.appArg!, e.appArg!)
  else
    none

@[inline] def app3? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity fName 3 then
    some (e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

@[inline] def app4? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 4 then
    some (e.appFn!.appFn!.appFn!.appArg!, e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

@[inline] def eq? (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3? ``Eq

@[inline] def ne? (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3? ``Ne

@[inline] def iff? (p : Expr) : Option (Expr × Expr) :=
  p.app2? ``Iff

@[inline] def eqOrIff? (p : Expr) : Option (Expr × Expr) :=
  if let some (_, lhs, rhs) := p.app3? ``Eq then
    some (lhs, rhs)
  else
    p.iff?

@[inline] def not? (p : Expr) : Option Expr :=
  p.app1? ``Not

@[inline] def notNot? (p : Expr) : Option Expr :=
  match p.not? with
  | some p => p.not?
  | none => none

@[inline] def and? (p : Expr) : Option (Expr × Expr) :=
  p.app2? ``And

@[inline] def heq? (p : Expr) : Option (Expr × Expr × Expr × Expr) :=
  p.app4? ``HEq

def natAdd? (e : Expr) : Option (Expr × Expr) :=
  e.app2? ``Nat.add

@[inline] def arrow? : Expr → Option (Expr × Expr)
  | Expr.forallE _ α β _ => if β.hasLooseBVars then none else some (α, β)
  | _                    => none

def isEq (e : Expr) :=
  e.isAppOfArity ``Eq 3

def isHEq (e : Expr) :=
  e.isAppOfArity ``HEq 4

def isIte (e : Expr) :=
  e.isAppOfArity ``ite 5

def isDIte (e : Expr) :=
  e.isAppOfArity ``dite 5

partial def listLit? (e : Expr) : Option (Expr × List Expr) :=
  let rec loop (e : Expr) (acc : List Expr) :=
    if e.isAppOfArity' ``List.nil 1 then
      some (e.appArg!', acc.reverse)
    else if e.isAppOfArity' ``List.cons 3 then
      loop e.appArg!' (e.appFn!'.appArg!' :: acc)
    else
      none
  loop e []

def arrayLit? (e : Expr) : Option (Expr × List Expr) :=
  if e.isAppOfArity' ``List.toArray 2 then
    listLit? e.appArg!'
  else
    none

/-- Recognize `α × β` -/
def prod? (e : Expr) : Option (Expr × Expr) :=
  e.app2? ``Prod

private def getConstructorVal? (env : Environment) (ctorName : Name) : Option ConstructorVal :=
  match env.find? ctorName with
  | some (ConstantInfo.ctorInfo v) => v
  | _                              => none

def isConstructorApp? (env : Environment) (e : Expr) : Option ConstructorVal :=
  match e with
  | Expr.lit (Literal.natVal n) => if n == 0 then getConstructorVal? env `Nat.zero else getConstructorVal? env `Nat.succ
  | _ =>
    match e.getAppFn with
    | Expr.const n _ => match getConstructorVal? env n with
      | some v => if v.numParams + v.numFields == e.getAppNumArgs then some v else none
      | none   => none
    | _ => none

def isConstructorApp (env : Environment) (e : Expr) : Bool :=
  e.isConstructorApp? env |>.isSome

/--
If `e` is a constructor application, return a pair containing the corresponding `ConstructorVal` and the constructor
application arguments.
This function treats numerals as constructors. For example, if `e` is the numeral `2`, the result pair
is `ConstructorVal` for `Nat.succ`, and the array `#[1]`. The parameter `useRaw` controls how the resulting
numeral is represented. If `useRaw := false`, then `mkNatLit` is used, otherwise `mkRawNatLit`.
Recall that `mkNatLit` uses the `OfNat.ofNat` application which is the canonical way of representing numerals
in the elaborator and tactic framework. We `useRaw := false` in the compiler (aka code generator).
-/
def constructorApp? (env : Environment) (e : Expr) (useRaw := false) : Option (ConstructorVal × Array Expr) := do
  match e with
  | Expr.lit (Literal.natVal n) =>
    if n == 0 then do
      let v ← getConstructorVal? env `Nat.zero
      pure (v, #[])
    else do
      let v ← getConstructorVal? env `Nat.succ
      pure (v, #[if useRaw then mkRawNatLit (n-1) else mkNatLit (n-1)])
  | _ =>
    match e.getAppFn with
    | Expr.const n _ => do
      let v ← getConstructorVal? env n
      if v.numParams + v.numFields == e.getAppNumArgs then
        pure (v, e.getAppArgs)
      else
        none
    | _ => none

end Lean.Expr

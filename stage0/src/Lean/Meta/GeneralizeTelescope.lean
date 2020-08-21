/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.KAbstract

namespace Lean
namespace Meta
namespace GeneralizeTelescope

structure Entry :=
(expr     : Expr)
(type     : Expr)
(modified : Bool)

partial def updateTypes (e newE : Expr) : Array Entry → Nat → MetaM (Array Entry)
| entries, i =>
  if h : i < entries.size then
    let entry := entries.get ⟨i, h⟩;
    match entry with
    | ⟨_, type, _⟩ => do
      typeAbst ← kabstract type e;
      if typeAbst.hasLooseBVars then do
        let typeNew := typeAbst.instantiate1 newE;
        let entries := entries.set ⟨i, h⟩ { entry with type := typeNew, modified := true };
        updateTypes entries (i+1)
      else
        updateTypes entries (i+1)
  else
    pure entries

partial def generalizeTelescopeAux {α} (prefixForNewVars : Name) (k : Array Expr → MetaM α) : Array Entry → Nat → Nat → Array Expr → MetaM α
| entries, i, nextVarIdx, fvars =>
  if h : i < entries.size then
    let replace (e : Expr) (type : Expr) : MetaM α := do {
      let userName := prefixForNewVars.appendIndexAfter nextVarIdx;
      withLocalDecl userName type BinderInfo.default $ fun x => do
        entries ← updateTypes e x entries (i+1);
        generalizeTelescopeAux entries (i+1) (nextVarIdx+1) (fvars.push x)
    };
    match entries.get ⟨i, h⟩ with
    | ⟨e@(Expr.fvar fvarId _), type, false⟩ => do
      localDecl ← getLocalDecl fvarId;
      match localDecl with
      | LocalDecl.cdecl _ _ _ _ _ => generalizeTelescopeAux entries (i+1) nextVarIdx (fvars.push e)
      | LocalDecl.ldecl _ _ _ _ _ => replace e type
    | ⟨e, type, modified⟩ => do
      when modified $ unlessM (isTypeCorrect type) $
        throwError $ "failed to create telescope generalizing " ++ (entries.map Entry.expr);
      replace e type
  else
    k fvars

end GeneralizeTelescope

open GeneralizeTelescope

/--
  Given expressions `es := #[e_1, e_2, ..., e_n]`, execute `k` with the
  free variables `(x_1 : A_1) (x_2 : A_2 [x_1]) ... (x_n : A_n [x_1, ... x_{n-1}])`.
  Moreover,
  - type of `e_1` is definitionally equal to `A_1`,
  - type of `e_2` is definitionally equal to `A_2[e_1]`.
  - ...
  - type of `e_n` is definitionally equal to `A_n[e_1, ..., e_{n-1}]`.

  This method tries to avoid the creation of new free variables. For example, if `e_i` is a
  free variable `x_i` and it is not a let-declaration variable, and its type does not depend on
  previous `e_j`s, the method will just use `x_i`.

  The telescope `x_1 ... x_n` can be used to create lambda and forall abstractions.
  Moreover, for any type correct lambda abstraction `f` constructed using `mkForall #[x_1, ..., x_n] ...`,
  The application `f e_1 ... e_n` is also type correct.

  The parameter `prefixForNewVars` is used to create new user facing names for the (new) variables `x_i`.

  The `kabstract` method is used to "locate" and abstract forward dependencies.
  That is, an occurrence of `e_i` in the of `e_j` for `j > i`.

  The method checks whether the abstract types `A_i` are type correct. Here is an example
  where `generalizeTelescope` fails to create the telescope `x_1 ... x_n`.
  Assume the local context contains `(n : Nat := 10) (xs : Vec Nat n) (ys : Vec Nat 10) (h : xs = ys)`.
  Then, assume we invoke `generalizeTelescope` with `es := #[10, xs, ys, h]` and `prefixForNewVars := aux`.
  A type error is detected when processing `h`'s type. At this point, the method had successfully produced
  ```
    (aux_1 : Nat) (xs : Vec Nat n) (aux_2 : Vec Nat aux_1)
  ```
  and the type for the new variable abstracting `h` is `xs = aux_2` which is not type correct. -/
def generalizeTelescope {α} (es : Array Expr) (prefixForNewVars : Name) (k : Array Expr → MetaM α) : MetaM α := do
es ← es.mapM $ fun e => do {
  type ← inferType e;
  type ← instantiateMVars type;
  pure { expr := e, type := type, modified := false : Entry }
};
generalizeTelescopeAux prefixForNewVars k es 0 1 #[]

end Meta
end Lean

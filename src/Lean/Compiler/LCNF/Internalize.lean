/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.Bind
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

private def refreshBinderName (binderName : Name) : CompilerM Name := do
  match binderName with
  | .num p _ =>
    let r := .num p (← get).nextIdx
    modify fun s => { s with nextIdx := s.nextIdx + 1 }
    return r
  | _ => return binderName

namespace Internalize

abbrev InternalizeM := StateRefT FVarSubst CompilerM

/--
The `InternalizeM` monad is a translator. It "translates" the free variables
in the input expressions and `Code`, into new fresh free variables in the
local context.
-/
instance : MonadFVarSubst InternalizeM true where
  getSubst := get

instance : MonadFVarSubstState InternalizeM where
  modifySubst := modify

private def mkNewFVarId (fvarId : FVarId) : InternalizeM FVarId := do
  let fvarId' ← Lean.mkFreshFVarId
  addFVarSubst fvarId fvarId'
  return fvarId'

def internalizeParam (p : Param) : InternalizeM Param := do
  let binderName ← refreshBinderName p.binderName
  let type ← normExpr p.type
  let fvarId ← mkNewFVarId p.fvarId
  let p := { p with binderName, fvarId, type }
  modifyLCtx fun lctx => lctx.addParam p
  return p

def internalizeLetDecl (decl : LetDecl) : InternalizeM LetDecl := do
  let binderName ← refreshBinderName decl.binderName
  let type ← normExpr decl.type
  let value ← normExpr decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := { decl with binderName, fvarId, type, value }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  return decl

mutual

partial def internalizeFunDecl (decl : FunDecl) : InternalizeM FunDecl := do
  let type ← normExpr decl.type
  let binderName ← refreshBinderName decl.binderName
  let params ← decl.params.mapM internalizeParam
  let value ← internalizeCode decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := { decl with binderName, fvarId, params, type, value }
  modifyLCtx fun lctx => lctx.addFunDecl decl
  return decl

partial def internalizeCode (code : Code) : InternalizeM Code := do
  match code with
  | .let decl k => return .let (← internalizeLetDecl decl) (← internalizeCode k)
  | .fun decl k => return .fun (← internalizeFunDecl decl) (← internalizeCode k)
  | .jp decl k => return .jp (← internalizeFunDecl decl) (← internalizeCode k)
  | .return fvarId => return .return (← normFVar fvarId)
  | .jmp fvarId args => return .jmp (← normFVar fvarId) (← args.mapM normExpr)
  | .unreach type => return .unreach (← normExpr type)
  | .cases c =>
    let resultType ← normExpr c.resultType
    let ensureAny := resultType != c.resultType && (resultType.isAnyType || resultType.isErased)
    /-
    Note:
    If the new result type for the cases is `⊤` or `◾`, we must add a cast to `⊤` (the any type)
    to every alternative if the resulting type is not `⊤`. This is similar to what we do at `ToLCNF.visitCases`.
    Here is an example to illustrate this issue.
    Suppose we have
    ```
    inductive Id {A : Type u} : A → A → Type u
      | refl {a : A} : Id a a
    def transport {A : Type u} (B : A → Type v) {a b : A} (p : Id a b) : B a → B b :=
    ```
    Its LCNF type is
    ```
    {A : Type u} (B : A → Type v) {a b : A} (p : Id ◾ ◾) (a.1 : B ◾) : B ◾
    ```
    and base phase code is
    ```
    cases p : B ◾
    | Id.refl =>
      a.1
    ```
    Now suppose we define
    ```
    def transportconst {A B : Type u} : A = B → A → B :=
      transport id
    ```
    By setting `B` as `id`, and then inlining `transport, we would have the following code for `transportconst` is
    ```
    cases p : ◾
    | Id.refl =>
      a.1
    ```
    Which can be checked by `Check.lean` because it assumes `◾` is compatible with anything and `a.1 : A`.
    However, if inline `transportconst`, we can hit type error since the continuation for transportconst is
    expecting a `B` instead of an `A`. We avoid this problem by adding a cast to `⊤`. See `ToLCNF.visitCases` for
    another place where we use this approach.
    Thus, the resulting code for `transportconst` is
    ```
    def MWE.transportconst (A : Type u) (B : Type u) (p : Id A B) (a.1 : A) :=
      cases p
      | Id.refl =>
        let _x.2 := @lcCast A ⊤ a.1
        _x.2
    ```
    -/
    let internalizeAltCode (k : Code) : InternalizeM Code := do
      let k ← internalizeCode k
      if ensureAny then
        k.ensureAnyType
      else
        return k
    let discr ← normFVar c.discr
    let alts ← c.alts.mapM fun
      | .alt ctorName params k => return .alt ctorName (← params.mapM internalizeParam) (← internalizeAltCode k)
      | .default k => return .default (← internalizeAltCode k)
    return .cases { c with discr, alts, resultType }

end

partial def internalizeCodeDecl (decl : CodeDecl) : InternalizeM CodeDecl := do
  match decl with
  | .let decl => return .let (← internalizeLetDecl decl)
  | .fun decl => return .fun (← internalizeFunDecl decl)
  | .jp decl => return .jp (← internalizeFunDecl decl)

end Internalize

/--
Refresh free variables ids in `code`, and store their declarations in the local context.
-/
partial def Code.internalize (code : Code) (s : FVarSubst := {}) : CompilerM Code :=
  Internalize.internalizeCode code |>.run' s

open Internalize in
def Decl.internalize (decl : Decl) (s : FVarSubst := {}): CompilerM Decl :=
  go decl |>.run' s
where
  go (decl : Decl) : InternalizeM Decl := do
    let type ← normExpr decl.type
    let params ← decl.params.mapM internalizeParam
    let value ← internalizeCode decl.value
    return { decl with type, params, value }

/--
Create a fresh local context and internalize the given decls.
-/
def cleanup (decl : Array Decl) : CompilerM (Array Decl) := do
  modify fun _ => {}
  decl.mapM fun decl => do
    modify fun s => { s with nextIdx := 1 }
    decl.internalize

end Lean.Compiler.LCNF
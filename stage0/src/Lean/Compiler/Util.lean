/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean.Compiler

def neutralExpr : Expr       := mkConst `_neutral
def unreachableExpr : Expr   := mkConst `_unreachable
def objectType : Expr        := mkConst `_obj
def voidType : Expr          := mkConst `_void
def mkLcProof (pred : Expr)  := mkApp (mkConst `lcProof []) pred

namespace atMostOnce

structure AtMostOnceData where
  found : Bool
  result : Bool

def Visitor := AtMostOnceData → AtMostOnceData

@[inline] def seq (f g : Visitor) : Visitor := fun d =>
  match f d with
  | ⟨found, false⟩ => ⟨found, false⟩
  | other          => g other

instance : AndThen Visitor where
  andThen a b := seq a (b ())

@[inline] def skip : Visitor := id

@[inline] def visitFVar (x y : FVarId) : Visitor
  | d@{result := false, ..} => d
  | {found := false, result := true} => {found := x == y, result := true}
  | {found := true,  result := true} => {found := true, result := x != y}

def visit (x : FVarId) : Expr → Visitor
  | Expr.fvar y _        => visitFVar y x
  | Expr.app f a _       => visit x a >> visit x f
  | Expr.lam _ d b _     => visit x d >> visit x b
  | Expr.forallE _ d b _ => visit x d >> visit x b
  | Expr.letE _ t v b _  => visit x t >> visit x v >> visit x b
  | Expr.mdata _ e _     => visit x e
  | Expr.proj _ _ e _    => visit x e
  | _                    => skip

end atMostOnce

open atMostOnce (visit) in
/-- Return true iff the free variable with id `x` occurs at most once in `e` -/
@[export lean_at_most_once]
def atMostOnce (e : Expr) (x : FVarId) : Bool :=
  let {result := result, ..} := visit x e {found := false, result := true}
  result

/- Helper functions for creating auxiliary names used in compiler passes. -/

@[export lean_mk_eager_lambda_lifting_name]
def mkEagerLambdaLiftingName (n : Name) (idx : Nat) : Name :=
  Name.mkStr n ("_elambda_" ++ toString idx)

@[export lean_is_eager_lambda_lifting_name]
def isEagerLambdaLiftingName : Name → Bool
  | Name.str p s _ => "_elambda".isPrefixOf s || isEagerLambdaLiftingName p
  | Name.num p _ _ => isEagerLambdaLiftingName p
  | _              => false

/-- Return the name of new definitions in the a given declaration.
    Here we consider only declarations we generate code for.
    We use this definition to implement `add_and_compile`. -/
@[export lean_get_decl_names_for_code_gen]
private def getDeclNamesForCodeGen : Declaration → List Name
  | Declaration.defnDecl { name := n, .. }   => [n]
  | Declaration.mutualDefnDecl defs          => defs.map fun d => d.name
  | Declaration.opaqueDecl { name := n, .. } => [n]
  | Declaration.axiomDecl { name := n, .. }  => [n] -- axiom may be tagged with `@[extern ...]`
  | _                                        => []

def checkIsDefinition (env : Environment) (n : Name) : Except String Unit :=
match env.find? n with
  | (some (ConstantInfo.defnInfo _))   => Except.ok ()
  | (some (ConstantInfo.opaqueInfo _)) => Except.ok ()
  | none => Except.error s!"unknow declaration '{n}'"
  | _    => Except.error s!"declaration is not a definition '{n}'"

/--
  We generate auxiliary unsafe definitions for regular recursive definitions.
  The auxiliary unsafe definition has a clear runtime cost execution model.
  This function returns the auxiliary unsafe definition name for the given name. -/
@[export lean_mk_unsafe_rec_name]
def mkUnsafeRecName (declName : Name) : Name :=
  Name.mkStr declName "_unsafe_rec"

/-- Return `some _` if the given name was created using `mkUnsafeRecName` -/
@[export lean_is_unsafe_rec_name]
def isUnsafeRecName? : Name → Option Name
  | Name.str n "_unsafe_rec" _ => some n
  | _ => none

end Lean.Compiler

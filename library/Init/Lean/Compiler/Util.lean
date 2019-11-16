/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean
namespace Compiler

def neutralExpr : Expr       := mkConst `_neutral
def unreachableExpr : Expr   := mkConst `_unreachable
def objectType : Expr        := mkConst `_obj
def voidType : Expr          := mkConst `_void
def mkLcProof (pred : Expr)  := mkApp (mkConst `lcProof []) pred

namespace atMostOnce

structure AtMostOnceData :=
(found result : Bool)

def Visitor := AtMostOnceData → AtMostOnceData

@[inline] def seq (f g : Visitor) : Visitor :=
fun d => match f d with
| ⟨found, false⟩ => ⟨found, false⟩
| other          => g other

instance : HasAndthen Visitor :=
⟨seq⟩

@[inline] def skip : Visitor := id

@[inline] def visitFVar (x y : Name) : Visitor
| d@{result := false, ..} => d
| {found := false, result := true} => {found := x == y, result := true}
| {found := true,  result := true} => {found := true, result := x != y}

def visit (x : Name) : Expr → Visitor
| Expr.fvar y _        => visitFVar y x
| Expr.app f a _       => visit a >> visit f
| Expr.lam _ d b _     => visit d >> visit b
| Expr.forallE _ d b _ => visit d >> visit b
| Expr.letE _ t v b _  => visit t >> visit v >> visit b
| Expr.mdata _ e _     => visit e
| Expr.proj _ _ e _    => visit e
| _                    => skip

end atMostOnce

/-- Return true iff the free variable with id `x` occurs at most once in `e` -/
@[export lean_at_most_once]
def atMostOnce (e : Expr) (x : Name) : Bool :=
let {result := result, ..} := atMostOnce.visit x e {found := false, result := true};
result

/- Helper functions for creating auxiliary names used in compiler passes. -/

@[export lean_mk_eager_lambda_lifting_name]
def mkEagerLambdaLiftingName (n : Name) (idx : Nat) : Name :=
Name.mkString n ("_elambda_" ++ toString idx)

@[export lean_is_eager_lambda_lifting_name]
def isEagerLambdaLiftingName : Name → Bool
| Name.mkString p s    => "_elambda".isPrefixOf s || isEagerLambdaLiftingName p
| Name.mkNumeral p _   => isEagerLambdaLiftingName p
| _ => false

/-- Return the name of new definitions in the a given declaration.
    Here we consider only declarations we generate code for.
    We use this definition to implement `add_and_compile`. -/
@[export lean_get_decl_names_for_code_gen]
private def getDeclNamesForCodeGen : Declaration → List Name
| Declaration.defnDecl { name := n, .. } => [n]
| Declaration.mutualDefnDecl defs        => defs.map $ fun d => d.name
| _                                      => []

def checkIsDefinition (env : Environment) (n : Name) : Except String Unit :=
match env.find n with
| (some (ConstantInfo.defnInfo _)) => Except.ok ()
| none => Except.error "unknow declaration"
| _    => Except.error "declaration is not a definition"

end Compiler
end Lean

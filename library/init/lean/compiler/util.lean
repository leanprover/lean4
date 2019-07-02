/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean
namespace Compiler

def neutralExpr : Expr       := Expr.const `_neutral []
def unreachableExpr : Expr   := Expr.const `_unreachable []
def objectType : Expr        := Expr.const `_obj []
def voidType : Expr          := Expr.const `_void []
def mkLcProof (pred : Expr)  := Expr.app (Expr.const `lcProof []) pred

namespace atMostOnce

structure AtMostOnceData :=
(found result : Bool)

def Visitor := AtMostOnceData → AtMostOnceData

@[inline] def seq (f g : Visitor) : Visitor :=
fun d => match f d with
| ⟨found, false⟩ := ⟨found, false⟩
| other          := g other

instance : HasAndthen Visitor :=
⟨seq⟩

@[inline] def skip : Visitor := id

@[inline] def visitFVar (x y : Name) : Visitor
| d@{result := false, ..} := d
| {found := false, result := true} := {found := x == y, result := true}
| {found := true,  result := true} := {found := true, result := x != y}

def visit (x : Name) : Expr → Visitor
| (Expr.fvar y)       := visitFVar y x
| (Expr.app f a)      := visit a >> visit f
| (Expr.lam _ _ d b)  := visit d >> visit b
| (Expr.pi _ _ d b)   := visit d >> visit b
| (Expr.elet _ t v b) := visit t >> visit v >> visit b
| (Expr.mdata _ e)    := visit e
| (Expr.proj _ _ e)   := visit e
| _                   := skip

end atMostOnce

/-- Return true iff the free variable with id `x` occurs at most once in `e` -/
@[export lean.at_most_once_core]
def atMostOnce (e : Expr) (x : Name) : Bool :=
let {result := result, ..} := atMostOnce.visit x e {found := false, result := true};
result

/- Helper functions for creating auxiliary names used in compiler passes. -/

@[export lean.mk_eager_lambda_lifting_name_core]
def mkEagerLambdaLiftingName (n : Name) (idx : Nat) : Name :=
Name.mkString n ("_elambda_" ++ toString idx)

@[export lean.is_eager_lambda_lifting_name_core]
def isEagerLambdaLiftingName : Name → Bool
| (Name.mkString p s)  := "_elambda".isPrefixOf s || isEagerLambdaLiftingName p
| (Name.mkNumeral p _) := isEagerLambdaLiftingName p
| _ := false

/-- Return the name of new definitions in the a given declaration.
    Here we consider only declarations we generate code for.
    We use this definition to implement `add_and_compile`. -/
@[export lean.get_decl_names_for_code_gen_core]
private def getDeclNamesForCodeGen : Declaration → List Name
| (Declaration.defnDecl { name := n, .. })   := [n]
| (Declaration.mutualDefnDecl defs)          := defs.map $ fun d => d.name
| _                                          := []

def checkIsDefinition (env : Environment) (n : Name) : Except String Unit :=
match env.find n with
| (some (ConstantInfo.defnInfo _)) := Except.ok ()
| none := Except.error "unknow declaration"
| _    := Except.error "declaration is not a definition"

end Compiler
end Lean

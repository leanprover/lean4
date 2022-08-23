/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean.Compiler.LCNF

structure Param where
  fvarId     : FVarId
  binderName : Name
  type       : Expr
  deriving Inhabited

inductive AltCore (Code : Type) where
  | alt (ctorName : Name) (params : Array Param) (code : Code)
  | default (code : Code)
  deriving Inhabited

structure LetDecl where
  fvarId : FVarId
  binderName : Name
  type : Expr
  value : Expr
  deriving Inhabited

structure FunDeclCore (Code : Type) where
  fvarId : FVarId
  binderName : Name
  params : Array Param
  type : Expr
  value : Code
  deriving Inhabited

structure CasesCore (Code : Type) where
  typeName : Name
  resultType : Expr
  discr : FVarId
  alts : Array (AltCore Code)
  deriving Inhabited

inductive Code where
  | let (decl : LetDecl) (k : Code)
  | fun (decl : FunDeclCore Code) (k : Code)
  | jp (decl : FunDeclCore Code) (k : Code)
  | jmp (fvarId : FVarId) (args : Array Expr)
  | cases (cases : CasesCore Code)
  | return (fvarId : FVarId)
  | unreach (type : Expr)
  deriving Inhabited

abbrev Alt := AltCore Code
abbrev FunDecl := FunDeclCore Code
abbrev Cases := CasesCore Code

/--
Declaration being processed by the Lean to Lean compiler passes.
-/
structure Decl where
  /--
  The name of the declaration from the `Environment` it came from
  -/
  name  : Name
  /--
  Universe level parameter names.
  -/
  levelParams : List Name
  /--
  The type of the declaration. Note that this is an erased LCNF type
  instead of the fully dependent one that might have been the original
  type of the declaration in the `Environment`.
  -/
  type  : Expr
  /--
  The value of the declaration, usually changes as it progresses
  through compiler passes.
  -/
  value : Code

end Lean.Compiler.LCNF

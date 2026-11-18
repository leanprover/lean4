/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
namespace Lean.Meta.Sym

/-- Returns the head of the conclusion of `type`, without using reduction. -/
def getConclusionHead : Expr → Expr
  | .letE _ _ _ b _  => getConclusionHead b
  | .forallE _ _ b _ => getConclusionHead b
  | .mdata _ b       => getConclusionHead b
  | .app f _         => getConclusionHead f
  | e                => e

def isClassHead? (env : Environment) (head : Expr) : Option Name :=
  match head with
  | .const n _ => if isClass env n then some n else none
  | _          => none

/--
Efficient version of `Meta.isClass?` for symbolic simulation. It does not use reduction, and it
instantiates metavariables only if the head of the conclusion of `type` is an assigned one.
-/
public def isClass? (type : Expr) : MetaM (Option Name) := do
  match getConclusionHead type with
  | .mvar mvarId =>
    unless (← mvarId.isAssigned <||> mvarId.isDelayedAssigned) do return none
    return isClassHead? (← getEnv) (getConclusionHead (← instantiateMVars type))
  | head => return isClassHead? (← getEnv) head

end Lean.Meta.Sym

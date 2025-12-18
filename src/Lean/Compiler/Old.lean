/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Environment
import Init.Data.String.TakeDrop

public section

namespace Lean
namespace Compiler

/-! Helper functions for creating auxiliary names used in (old) compiler passes. -/

def mkEagerLambdaLiftingName (n : Name) (idx : Nat) : Name :=
  Name.mkStr n ("_elambda_" ++ toString idx)

def isEagerLambdaLiftingName : Name → Bool
  | .str p s => "_elambda".isPrefixOf s || isEagerLambdaLiftingName p
  | .num p _ => isEagerLambdaLiftingName p
  | _        => false

/-- Return the name of new definitions in the a given declaration.
    Here we consider only declarations we generate code for.
    We use this definition to implement `add_and_compile`. -/
def getDeclNamesForCodeGen : Declaration → Array Name
  | .defnDecl { name, .. }   => #[name]
  | .opaqueDecl { name, .. } => #[name]
  | .axiomDecl { name, .. }  => #[name] -- axiom may be tagged with `@[extern ...]`
  | .mutualDefnDecl defs     => defs.toArray.map (·.name)
  | _                        => #[]

def checkIsDefinition (env : Environment) (n : Name) : Except String Unit := do
  let some info := env.findAsync? n
    | throw s!"Unknown declaration `{n}`"
  unless info.kind matches .defn | .opaque do
    throw s!"Declaration `{n}` is not a definition"

/--
  We generate auxiliary unsafe definitions for regular recursive definitions.
  The auxiliary unsafe definition has a clear runtime cost execution model.
  This function returns the auxiliary unsafe definition name for the given name. -/
def mkUnsafeRecName (declName : Name) : Name :=
  Name.mkStr declName "_unsafe_rec"

/-- Return `some _` if the given name was created using `mkUnsafeRecName` -/
def isUnsafeRecName? : Name → Option Name
  | .str n "_unsafe_rec" => some n
  | _ => none

end Compiler

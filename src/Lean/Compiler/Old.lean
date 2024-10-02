/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment

namespace Lean
namespace Compiler

/-! Helper functions for creating auxiliary names used in (old) compiler passes. -/

@[export lean_mk_eager_lambda_lifting_name]
def mkEagerLambdaLiftingName (n : Name) (idx : Nat) : Name :=
  Name.mkStr n ("_elambda_" ++ toString idx)

@[export lean_is_eager_lambda_lifting_name]
def isEagerLambdaLiftingName : Name → Bool
  | .str p s => "_elambda".isPrefixOf s || isEagerLambdaLiftingName p
  | .num p _ => isEagerLambdaLiftingName p
  | _        => false

/-- Return the name of new definitions in the a given declaration.
    Here we consider only declarations we generate code for.
    We use this definition to implement `add_and_compile`. -/
def getDeclNamesForCodeGen : Declaration → List Name
  | Declaration.defnDecl { name := n, .. }   => [n]
  | Declaration.mutualDefnDecl defs          => defs.map fun d => d.name
  | Declaration.opaqueDecl { name := n, .. } => [n]
  | Declaration.axiomDecl { name := n, .. }  => [n] -- axiom may be tagged with `@[extern ...]`
  | _                                        => []

def checkIsDefinition (env : Environment) (n : Name) : Except String Unit :=
match env.find? n with
  | (some (ConstantInfo.defnInfo _))   => Except.ok ()
  | (some (ConstantInfo.opaqueInfo _)) => Except.ok ()
  | none => Except.error s!"unknown declaration '{n}'"
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
  | .str n "_unsafe_rec" => some n
  | _ => none

end Compiler

namespace Environment

/--
Compile the given block of mutual declarations.
Assumes the declarations have already been added to the environment using `addDecl`.
-/
@[extern "lean_compile_decls"]
opaque compileDecls (env : Environment) (opt : @& Options) (decls : @& List Name) : Except Kernel.Exception Environment

/-- Compile the given declaration, it assumes the declaration has already been added to the environment using `addDecl`. -/
def compileDecl (env : Environment) (opt : @& Options) (decl : @& Declaration) : Except Kernel.Exception Environment :=
  compileDecls env opt (Compiler.getDeclNamesForCodeGen decl)

end Environment

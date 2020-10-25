/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Exception

namespace Lean

section Methods

variables {m : Type → Type} [MonadEnv m]

def setEnv (env : Environment) : m Unit :=
  modifyEnv fun _ => env

@[inline] def withoutModifyingEnv [Monad m] [MonadFinally m] {α : Type} (x : m α) : m α := do
  let env ← getEnv
  try x finally setEnv env

@[inline] def matchConst [Monad m] {α : Type} (e : Expr) (failK : Unit → m α) (k : ConstantInfo → List Level → m α) : m α := do
  match e with
  | Expr.const constName us _ => do
    match (← getEnv).find? constName with
    | some cinfo => k cinfo us
    | none       => failK ()
  | _ => failK ()

@[inline] def matchConstInduct [Monad m] {α : Type} (e : Expr) (failK : Unit → m α) (k : InductiveVal → List Level → m α) : m α :=
  matchConst e failK fun cinfo us =>
    match cinfo with
    | ConstantInfo.inductInfo val => k val us
    | _                           => failK ()

@[inline] def matchConstCtor [Monad m] {α : Type} (e : Expr) (failK : Unit → m α) (k : ConstructorVal → List Level → m α) : m α :=
  matchConst e failK fun cinfo us =>
    match cinfo with
    | ConstantInfo.ctorInfo val => k val us
    | _                         => failK ()

@[inline] def matchConstRec [Monad m] {α : Type} (e : Expr) (failK : Unit → m α) (k : RecursorVal → List Level → m α) : m α :=
  matchConst e failK fun cinfo us =>
    match cinfo with
    | ConstantInfo.recInfo val => k val us
    | _                        => failK ()

section
variables [Monad m]

def hasConst (constName : Name) : m Bool := do
  return (← getEnv).contains constName

private partial def mkAuxNameAux (env : Environment) (base : Name) (i : Nat) : Name :=
  let candidate := base.appendIndexAfter i
  if env.contains candidate then
    mkAuxNameAux env base (i+1)
  else
    candidate

def mkAuxName (baseName : Name) (idx : Nat) : m Name := do
  return mkAuxNameAux (← getEnv) baseName idx

variables [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]

def getConstInfo (constName : Name) : m ConstantInfo := do
  match (← getEnv).find? constName with
  | some info => pure info
  | none      => throwError! "unknown constant '{mkConst constName}'"

def getConstInfoInduct (constName : Name) : m InductiveVal := do
  match (← getConstInfo constName) with
  | ConstantInfo.inductInfo v => pure v
  | _                         => throwError! "'{mkConst constName}' is not a inductive type"

def getConstInfoCtor (constName : Name) : m ConstructorVal := do
  match (← getConstInfo constName) with
  | ConstantInfo.ctorInfo v => pure v
  | _                       => throwError! "'{mkConst constName}' is not a constructor"

def getConstInfoRec (constName : Name) : m RecursorVal := do
  match (← getConstInfo constName) with
  | ConstantInfo.recInfo v => pure v
  | _                      => throwError! "'{mkConst constName}' is not a recursor"

@[inline] def matchConstStruct {α : Type} (e : Expr) (failK : Unit → m α) (k : InductiveVal → List Level → ConstructorVal → m α) : m α :=
  matchConstInduct e failK fun ival us => do
    if ival.isRec then failK ()
    else match ival.ctors with
      | [ctor] =>
        match (← getConstInfo ctor) with
        | ConstantInfo.ctorInfo cval => k ival us cval
        | _ => failK ()
      | _ => failK ()

def addDecl [MonadOptions m] (decl : Declaration) : m Unit := do
  match (← getEnv).addDecl decl with
  | Except.ok    env => setEnv env
  | Except.error ex  => throwKernelException ex

def compileDecl [MonadOptions m] (decl : Declaration) : m Unit := do
  match (← getEnv).compileDecl (← getOptions) decl with
  | Except.ok env   => setEnv env
  | Except.error ex => throwKernelException ex

def addAndCompile [MonadOptions m] (decl : Declaration) : m Unit := do
  addDecl decl;
  compileDecl decl

variables [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] [MonadOptions m]

unsafe def evalConst (α) (constName : Name) : m α := do
  ofExcept $ (← getEnv).evalConst α (← getOptions) constName

unsafe def evalConstCheck (α) (typeName : Name) (constName : Name) : m α := do
  ofExcept $ (← getEnv).evalConstCheck α (← getOptions) typeName constName

end

end Methods
end Lean

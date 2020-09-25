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
env ← getEnv;
finally x (setEnv env)

@[inline] def matchConst [Monad m] {α : Type} (e : Expr) (failK : Unit → m α) (k : ConstantInfo → List Level → m α) : m α := do
match e with
| Expr.const constName us _ => do
  env ← getEnv;
  match env.find? constName with
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
env ← getEnv;
pure $ env.contains constName

private partial def mkAuxNameAux (env : Environment) (base : Name) : Nat → Name
| i =>
  let candidate := base.appendIndexAfter i;
  if env.contains candidate then
    mkAuxNameAux (i+1)
  else
    candidate

def mkAuxName (baseName : Name) (idx : Nat) : m Name := do
env ← getEnv;
pure $ mkAuxNameAux env baseName idx

variables [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]

def getConstInfo (constName : Name) : m ConstantInfo := do
env ← getEnv;
match env.find? constName with
| some info => pure info
| none      => throwError ("unknown constant '" ++ constName ++ "'")

def getConstInfoInduct (constName : Name) : m InductiveVal := do
info ← getConstInfo constName;
match info with
| ConstantInfo.inductInfo v => pure v
| _                         => throwError ("'" ++ constName ++ "' is not a inductive type")

def getConstInfoCtor (constName : Name) : m ConstructorVal := do
info ← getConstInfo constName;
match info with
| ConstantInfo.ctorInfo v => pure v
| _                       => throwError ("'" ++ constName ++ "' is not a constructor")

def getConstInfoRec (constName : Name) : m RecursorVal := do
info ← getConstInfo constName;
match info with
| ConstantInfo.recInfo v => pure v
| _                      => throwError ("'" ++ constName ++ "' is not a recursor")

@[inline] def matchConstStruct {α : Type} (e : Expr) (failK : Unit → m α) (k : InductiveVal → List Level → ConstructorVal → m α) : m α :=
matchConstInduct e failK fun ival us =>
  if ival.isRec then failK ()
  else match ival.ctors with
    | [ctor] => do
      ctorInfo ← getConstInfo ctor;
      match ctorInfo with
      | ConstantInfo.ctorInfo cval => k ival us cval
      | _ => failK ()
    | _ => failK ()

def addDecl [MonadOptions m] (decl : Declaration) : m Unit := do
env ← getEnv;
match env.addDecl decl with
| Except.ok    env => setEnv env
| Except.error ex  => throwKernelException ex

def compileDecl [MonadOptions m] (decl : Declaration) : m Unit := do
env  ← getEnv;
opts ← getOptions;
match env.compileDecl opts decl with
| Except.ok env   => setEnv env
| Except.error ex => throwKernelException ex

def addAndCompile [MonadOptions m] (decl : Declaration) : m Unit := do
addDecl decl;
compileDecl decl

variables [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]

unsafe def evalConst (α) (constName : Name) : m α := do
env ← getEnv;
ofExcept $ env.evalConst α constName

unsafe def evalConstCheck (α) (typeName : Name) (constName : Name) : m α := do
env ← getEnv;
ofExcept $ env.evalConstCheck α typeName constName

end

end Methods
end Lean

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Exception
import Lean.Declaration
import Lean.Util.FindExpr
import Lean.AuxRecursor

namespace Lean

def setEnv [MonadEnv m] (env : Environment) : m Unit :=
  modifyEnv fun _ => env

def isInductive [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getEnv).find? declName with
  | some (ConstantInfo.inductInfo ..) => return true
  | _ => return false

def isInductivePredicate [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  match (← getEnv).find? declName with
  | some (ConstantInfo.inductInfo { type := type, ..}) => return visit type
  | _ => return false
where
  visit : Expr → Bool
    | Expr.sort u ..       => u == levelZero
    | Expr.forallE _ _ b _ => visit b
    | _                    => false

def isRecCore (env : Environment) (declName : Name) : Bool :=
  match env.find? declName with
  | some (ConstantInfo.recInfo ..) => return true
  | _ => return false

def isRec [Monad m] [MonadEnv m] (declName : Name) : m Bool :=
  return isRecCore (← getEnv) declName

@[inline] def withoutModifyingEnv [Monad m] [MonadEnv m] [MonadFinally m] {α : Type} (x : m α) : m α := do
  let env ← getEnv
  try x finally setEnv env

@[inline] def matchConst [Monad m] [MonadEnv m] (e : Expr) (failK : Unit → m α) (k : ConstantInfo → List Level → m α) : m α := do
  match e with
  | Expr.const constName us _ => do
    match (← getEnv).find? constName with
    | some cinfo => k cinfo us
    | none       => failK ()
  | _ => failK ()

@[inline] def matchConstInduct [Monad m] [MonadEnv m] (e : Expr) (failK : Unit → m α) (k : InductiveVal → List Level → m α) : m α :=
  matchConst e failK fun cinfo us =>
    match cinfo with
    | ConstantInfo.inductInfo val => k val us
    | _                           => failK ()

@[inline] def matchConstCtor [Monad m] [MonadEnv m] (e : Expr) (failK : Unit → m α) (k : ConstructorVal → List Level → m α) : m α :=
  matchConst e failK fun cinfo us =>
    match cinfo with
    | ConstantInfo.ctorInfo val => k val us
    | _                         => failK ()

@[inline] def matchConstRec [Monad m] [MonadEnv m] (e : Expr) (failK : Unit → m α) (k : RecursorVal → List Level → m α) : m α :=
  matchConst e failK fun cinfo us =>
    match cinfo with
    | ConstantInfo.recInfo val => k val us
    | _                        => failK ()

def hasConst [Monad m] [MonadEnv m] (constName : Name) : m Bool := do
  return (← getEnv).contains constName

private partial def mkAuxNameAux (env : Environment) (base : Name) (i : Nat) : Name :=
  let candidate := base.appendIndexAfter i
  if env.contains candidate then
    mkAuxNameAux env base (i+1)
  else
    candidate

def mkAuxName [Monad m] [MonadEnv m] (baseName : Name) (idx : Nat) : m Name := do
  return mkAuxNameAux (← getEnv) baseName idx

def getConstInfo [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m ConstantInfo := do
  match (← getEnv).find? constName with
  | some info => pure info
  | none      => throwError "unknown constant '{mkConst constName}'"

def mkConstWithLevelParams [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m Expr := do
  let info ← getConstInfo constName
  mkConst constName (info.levelParams.map mkLevelParam)

def getConstInfoInduct [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m InductiveVal := do
  match (← getConstInfo constName) with
  | ConstantInfo.inductInfo v => pure v
  | _                         => throwError "'{mkConst constName}' is not a inductive type"

def getConstInfoCtor [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m ConstructorVal := do
  match (← getConstInfo constName) with
  | ConstantInfo.ctorInfo v => pure v
  | _                       => throwError "'{mkConst constName}' is not a constructor"

def getConstInfoRec [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m RecursorVal := do
  match (← getConstInfo constName) with
  | ConstantInfo.recInfo v => pure v
  | _                      => throwError "'{mkConst constName}' is not a recursor"

@[inline] def matchConstStruct [Monad m] [MonadEnv m] [MonadError m] (e : Expr) (failK : Unit → m α) (k : InductiveVal → List Level → ConstructorVal → m α) : m α :=
  matchConstInduct e failK fun ival us => do
    if ival.isRec then failK ()
    else match ival.ctors with
      | [ctor] =>
        match (← getConstInfo ctor) with
        | ConstantInfo.ctorInfo cval => k ival us cval
        | _ => failK ()
      | _ => failK ()

def addDecl [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (decl : Declaration) : m Unit := do
  match (← getEnv).addDecl decl with
  | Except.ok    env => setEnv env
  | Except.error ex  => throwKernelException ex

private def supportedRecursors :=
  #[``Empty.rec, ``False.rec, ``Eq.ndrec, ``Eq.rec, ``Eq.recOn, ``Eq.casesOn, ``False.casesOn, ``Empty.casesOn, ``And.rec, ``And.casesOn]

/- This is a temporary workaround for generating better error messages for the compiler. It can be deleted after we
   rewrite the remaining parts of the compiler in Lean.  -/
private def checkUnsupported [Monad m] [MonadEnv m] [MonadError m] (decl : Declaration) : m Unit := do
  let env ← getEnv
  decl.forExprM fun e =>
    let unsupportedRecursor? := e.find? fun
      | Expr.const declName .. =>
        ((isAuxRecursor env declName && !isCasesOnRecursor env declName) || isRecCore env declName)
        && !supportedRecursors.contains declName
      | _ => false
    match unsupportedRecursor? with
    | some (Expr.const declName ..) => throwError "code generator does not support recursor '{declName}' yet, consider using 'match ... with' and/or structural recursion"
    | _ => pure ()

def compileDecl [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (decl : Declaration) : m Unit := do
  match (← getEnv).compileDecl (← getOptions) decl with
  | Except.ok env   => setEnv env
  | Except.error (KernelException.other msg) =>
    checkUnsupported decl -- Generate nicer error message for unsupported recursors and axioms
    throwError msg
  | Except.error ex =>
    throwKernelException ex

def addAndCompile [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (decl : Declaration) : m Unit := do
  addDecl decl;
  compileDecl decl

unsafe def evalConst [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (α) (constName : Name) : m α := do
  ofExcept <| (← getEnv).evalConst α (← getOptions) constName

unsafe def evalConstCheck [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (α) (typeName : Name) (constName : Name) : m α := do
  ofExcept <| (← getEnv).evalConstCheck α (← getOptions) typeName constName

def findModuleOf? [Monad m] [MonadEnv m] [MonadError m] (declName : Name) : m (Option Name) := do
  discard <| getConstInfo declName -- ensure declaration exists
  match (← getEnv).getModuleIdxFor? declName with
  | none        => return none
  | some modIdx => return some ((← getEnv).allImportedModuleNames[modIdx])

def isEnumType  [Monad m] [MonadEnv m] [MonadError m] (declName : Name) : m Bool := do
  if let ConstantInfo.inductInfo info ← getConstInfo declName then
    if info.all.length == 1 && info.numIndices == 0 && info.numParams == 0
       && !info.ctors.isEmpty && !info.isRec && !info.isNested && !info.isUnsafe then
      info.ctors.allM fun ctorName => do
        let ConstantInfo.ctorInfo info ← getConstInfo ctorName | return false
        return info.numFields == 0
    else
      return false
  else
    return false

end Lean

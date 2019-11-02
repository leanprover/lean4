/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean

/- Given a structure `S`, Lean automatically creates an auxiliary definition (projection function)
   for each field. This structure caches information about these auxiliary definitions. -/
structure ProjectionFunctionInfo :=
(ctorName : Name)      -- Constructor associated with the auxiliary projection function.
(nparams : Nat)    -- Number of parameters in the structure
(i : Nat)          -- The field index associated with the auxiliary projection function.
(fromClass : Bool) -- `true` if the structure is a class

instance ProjectionFunctionInfo.inhabited : Inhabited ProjectionFunctionInfo :=
⟨{ ctorName := default _, nparams := default _, i := 0, fromClass := false }⟩

def mkProjectionFnInfoExtension : IO (SimplePersistentEnvExtension (Name × ProjectionFunctionInfo) (NameMap ProjectionFunctionInfo)) :=
registerSimplePersistentEnvExtension {
  name          := `projinfo,
  addImportedFn := fun as => {},
  addEntryFn    := fun s p => s.insert p.1 p.2,
  toArrayFn     := fun es => es.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
}

@[init mkProjectionFnInfoExtension]
constant projectionFnInfoExt : SimplePersistentEnvExtension (Name × ProjectionFunctionInfo) (NameMap ProjectionFunctionInfo) := default _

@[export lean_add_projection_info]
def addProjectionFnInfo (env : Environment) (projName : Name) (ctorName : Name) (nparams : Nat) (i : Nat) (fromClass : Bool) : Environment :=
projectionFnInfoExt.addEntry env (projName, { ctorName := ctorName, nparams := nparams, i := i, fromClass := fromClass })

namespace Environment

@[export lean_get_projection_info]
def getProjectionFnInfo (env : Environment) (projName : Name) : Option ProjectionFunctionInfo :=
match env.getModuleIdxFor projName with
| some modIdx =>
  match (projectionFnInfoExt.getModuleEntries env modIdx).binSearch (projName, default _) (fun a b => Name.quickLt a.1 b.1) with
  | some e => some e.2
  | none   => none
| none        => (projectionFnInfoExt.getState env).find projName

def isProjectionFn (env : Environment) (n : Name) : Bool :=
match env.getModuleIdxFor n with
| some modIdx => (projectionFnInfoExt.getModuleEntries env modIdx).binSearchContains (n, default _) (fun a b => Name.quickLt a.1 b.1)
| none        => (projectionFnInfoExt.getState env).contains n

@[specialize] def reduceProjectionFnAux {α} {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (env : Environment) (projInfo : ProjectionFunctionInfo) (projArgs : Array Expr)
    (failK : Unit → m α)
    (successK : Expr → m α) : m α :=
let majorIdx := projInfo.nparams;
if h : majorIdx < projArgs.size then do
  let major := projArgs.get ⟨majorIdx, h⟩;
  major ← whnf major;
  matchConst env major.getAppFn failK $ fun majorInfo majorLvls =>
    let i := projInfo.nparams + projInfo.i;
    if i < major.getAppNumArgs then
      successK $ mkAppRange (major.getArg! i) (majorIdx + 1) projArgs.size projArgs
    else
      failK ()
else
  failK ()

@[specialize] def reduceProjectionFn {α} {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (env : Environment) (e : Expr)
    (failK : Unit → m α)
    (successK : Expr → m α) : m α :=
matchConst env e.getAppFn failK $ fun cinfo _ =>
  match getProjectionFnInfo env cinfo.name with
  | some projInfo => reduceProjectionFnAux whnf env projInfo e.getAppArgs failK successK
  | none => failK ()

end Environment
end Lean

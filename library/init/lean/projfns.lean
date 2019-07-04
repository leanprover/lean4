/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

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

@[export lean.add_projection_info_core]
def addProjectionFnInfo (env : Environment) (projName : Name) (ctorName : Name) (nparams : Nat) (i : Nat) (fromClass : Bool) : Environment :=
projectionFnInfoExt.addEntry env (projName, { ctorName := ctorName, nparams := nparams, i := i, fromClass := fromClass })

namespace Environment

@[export lean.get_projection_info_core]
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

end Environment
end Lean

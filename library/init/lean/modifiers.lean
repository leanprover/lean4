/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean

def mkProtectedExtension : IO (PersistentEnvExtension Name NameSet) :=
registerPersistentEnvExtension {
  name       := `protected,
  initState  := {},
  addEntryFn := λ init s n, if init then s else s.insert n,
  toArrayFn  := λ es, es.toArray.qsort Name.quickLt,
  lazy       := false }

@[init mkProtectedExtension]
constant protectedExt : PersistentEnvExtension Name NameSet := default _

@[export lean.add_protected_core]
def addProtected (env : Environment) (n : Name) : Environment :=
protectedExt.addEntry env n

@[export lean.is_protected_core]
def isProtected (env : Environment) (n : Name) : Bool :=
match env.getModuleIdxFor n with
| some modIdx := ((protectedExt.getModuleEntries env modIdx).binSearch n Name.quickLt).isSome
| none        := (protectedExt.getState env).contains n

end Lean

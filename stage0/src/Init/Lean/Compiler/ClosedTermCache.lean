/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean

abbrev ClosedTermCache := SMap Expr Name

def mkClosedTermCacheExtension : IO (SimplePersistentEnvExtension (Expr × Name) ClosedTermCache) :=
registerSimplePersistentEnvExtension {
  name       := `closedTermCache,
  addImportedFn := fun as =>
    let cache : ClosedTermCache := mkStateFromImportedEntries (fun s (p : Expr × Name) => s.insert p.1 p.2) {} as;
    cache.switch,
  addEntryFn := fun s ⟨e, n⟩ => s.insert e n
}

@[init mkClosedTermCacheExtension]
constant closedTermCacheExt : SimplePersistentEnvExtension (Expr × Name) ClosedTermCache := arbitrary _

@[export lean_cache_closed_term_name]
def cacheClosedTermName (env : Environment) (e : Expr) (n : Name) : Environment :=
closedTermCacheExt.addEntry env (e, n)

@[export lean_get_closed_term_name]
def getClosedTermName? (env : Environment) (e : Expr) : Option Name :=
(closedTermCacheExt.getState env).find? e

end Lean

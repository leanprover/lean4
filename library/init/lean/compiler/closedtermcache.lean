/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean

abbrev ClosedTermCache := SMap Expr Name Expr.quickLt

def mkClosedTermCacheExtension : IO (SimplePersistentEnvExtension (Expr × Name) ClosedTermCache) :=
registerSimplePersistentEnvExtension {
  name       := `closedTermCache,
  addImportedFn := λ as,
    let cache : ClosedTermCache := mkStateFromImportedEntries (λ s (p : Expr × Name), s.insert p.1 p.2) {} as in
    cache.switch,
  addEntryFn := λ s ⟨e, n⟩, s.insert e n
}

@[init mkClosedTermCacheExtension]
constant closedTermCacheExt : SimplePersistentEnvExtension (Expr × Name) ClosedTermCache := default _

@[export lean.cache_closed_term_name_core]
def cacheClosedTermName (env : Environment) (e : Expr) (n : Name) : Environment :=
closedTermCacheExt.addEntry env (e, n)

@[export lean.get_closed_term_name_core]
def getClosedTermName (env : Environment) (e : Expr) : Option Name :=
(closedTermCacheExt.getState env).find e

end Lean

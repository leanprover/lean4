/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment

namespace Lean

abbrev ClosedTermCache := SMap Expr Name Expr.quickLt

def mkClosedTermCacheExtension : IO (PersistentEnvExtension (Expr × Name) ClosedTermCache) :=
registerPersistentEnvExtension {
  name       := `closedTermCache,
  initState  := {},
  addEntryFn := λ init s ⟨e, n⟩,
    let s := if init then s else s.switch in
    s.insert e n,
  lazy       := false }

@[init mkClosedTermCacheExtension]
constant closedTermCacheExt : PersistentEnvExtension (Expr × Name) ClosedTermCache := default _

@[export lean.cache_closed_term_name_core]
def cacheClosedTermName (env : Environment) (e : Expr) (n : Name) : Environment :=
closedTermCacheExt.addEntry env (e, n)

@[export lean.get_closed_term_name]
def getClosedTermName (env : Environment) (e : Expr) : Option Name :=
(closedTermCacheExt.getState env).find e

end Lean

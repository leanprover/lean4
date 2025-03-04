/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment

namespace Lean

structure ClosedTermCache where
  map        : PHashMap Expr Name := {}
  constNames : NameSet := {}
  deriving Inhabited

builtin_initialize closedTermCacheExt : EnvExtension ClosedTermCache ←
  registerEnvExtension (pure {}) (asyncMode := .sync)  -- compilation is non-parallel anyway

@[export lean_cache_closed_term_name]
def cacheClosedTermName (env : Environment) (e : Expr) (n : Name) : Environment :=
  closedTermCacheExt.modifyState env fun s => { s with map := s.map.insert e n, constNames := s.constNames.insert n }

@[export lean_get_closed_term_name]
def getClosedTermName? (env : Environment) (e : Expr) : Option Name :=
  (closedTermCacheExt.getState env).map.find? e

def isClosedTermName (env : Environment) (n : Name) : Bool :=
  (closedTermCacheExt.getState env).constNames.contains n

end Lean

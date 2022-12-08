/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MonadEnv

namespace Lean

structure LazyInitExtension (m : Type → Type) (α : Type) where
  ext : EnvExtension (Option α)
  fn  : m α

instance [Monad m] [Inhabited α] : Inhabited (LazyInitExtension m α) where
  default := {
    ext := default
    fn  := pure default
  }

/--
  Register an environment extension for storing the result of `fn`.
  We initialize the extension with `none`, and `fn` is executed the
  first time `LazyInit.get` is executed.

  This kind of extension is useful for avoiding work duplication in
  scenarios where a thunk cannot be used because the computation depends
  on state from the `m` monad. For example, we may want to "cache" a collection
  of theorems as a `SimpLemmas` object.  -/
def registerLazyInitExtension (fn : m α) : IO (LazyInitExtension m α) := do
  let ext ← registerEnvExtension (pure none)
  return { ext, fn }

def LazyInitExtension.get [MonadEnv m] [Monad m] (init : LazyInitExtension m α) : m α := do
  match init.ext.getState (← getEnv) with
  | some a => return a
  | none   =>
    let a ← init.fn
    modifyEnv fun env => init.ext.setState env (some a)
    return a

end Lean

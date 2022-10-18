/-
Copyright (c) 2019 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
import Lean.Data.Options

namespace Lean

/-- Print and accumulate run time of `act` when option `profiler` is set to `true`. -/
@[extern "lean_profileit"]
def profileit {α : Type} (category : @& String) (opts : @& Options) (fn : Unit → α) : α := fn ()

unsafe def profileitIOUnsafe {ε α : Type} (category : String) (opts : Options) (act : EIO ε α) : EIO ε α :=
  match profileit category opts fun _ => unsafeEIO act with
  | Except.ok a    => pure a
  | Except.error e => throw e

@[implemented_by profileitIOUnsafe]
def profileitIO {ε α : Type} (category : String) (opts : Options) (act : EIO ε α) : EIO ε α := act

-- impossible to infer `ε`
def profileitM {m : Type → Type} (ε : Type) [MonadFunctorT (EIO ε) m] {α : Type} (category : String) (opts : Options) (act : m α) : m α :=
  monadMap (fun {β} => profileitIO (ε := ε) (α := β) category opts) act

end Lean

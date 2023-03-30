/-
Copyright (c) 2019 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
import Lean.Data.Options

namespace Lean

register_builtin_option profiler : Bool := {
  defValue := false
  group    := "profiler"
  descr    := "show execution times of various Lean components"
}

register_builtin_option profiler.threshold : Nat := {
  defValue := 100
  group    := "profiler"
  descr    := "threshold in milliseconds, profiling times under threshold will not be reported individually"
}

@[export lean_get_profiler]
private def get_profiler (o : Options) : Bool :=
  profiler.get o

@[export lean_get_profiler_threshold]
def profiler.threshold.getSecs (o : Options) : Float :=
  (profiler.threshold.get o).toFloat / 1000

/-- Print and accumulate run time of `act` when option `profiler` is set to `true`. -/
@[extern "lean_profileit"]
def profileit {α : Type} (category : @& String) (opts : @& Options) (fn : Unit → α) (decl := Name.anonymous) : α := fn ()

unsafe def profileitIOUnsafe {ε α : Type} (category : String) (opts : Options) (act : EIO ε α) (decl := Name.anonymous) : EIO ε α :=
  match profileit (decl := decl) category opts fun _ => unsafeEIO act with
  | Except.ok a    => pure a
  | Except.error e => throw e

@[implemented_by profileitIOUnsafe]
def profileitIO {ε α : Type} (category : String) (opts : Options) (act : EIO ε α) (decl := Name.anonymous) : EIO ε α := act

-- impossible to infer `ε`
def profileitM {m : Type → Type} (ε : Type) [MonadFunctorT (EIO ε) m] {α : Type} (category : String) (opts : Options) (act : m α) (decl := Name.anonymous) : m α :=
  monadMap (fun {β} => profileitIO (ε := ε) (α := β) (decl := decl) category opts) act

end Lean

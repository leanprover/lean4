/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Data.UInt.Basic

namespace Lake

/-- A process exit / return code. -/
abbrev ExitCode := UInt32

class MonadExit (m : Type u → Type v) where
  exit {α : Type u} : ExitCode → m α

export MonadExit (exit)

instance [MonadLift m n] [MonadExit m] : MonadExit n where
  exit rc := liftM (m := m) <| exit rc

/-- Exit with `ExitCode` if it is not 0. Otherwise, continue. -/
@[inline] def exitIfErrorCode [Pure m] [MonadExit m]  (rc : ExitCode) : m Unit :=
  if rc != 0 then exit rc else pure ()

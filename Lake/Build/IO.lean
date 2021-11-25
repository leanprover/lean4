/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Error
import Lake.Util.OptionIO

namespace Lake

abbrev BuildIO :=
  LogMethodsT BaseIO OptionIO

namespace BuildIO

def run (logMethods : LogMethods BaseIO) (self : BuildIO α) : IO α :=
  ReaderT.run self logMethods |>.toIO fun _ => IO.userError "build failed"

def runWith (logMethods : LogMethods BaseIO) (self : BuildIO α) : OptionIO α :=
  ReaderT.run self logMethods

instance : MonadError BuildIO := ⟨MonadLog.error⟩
instance : MonadLift IO BuildIO := ⟨MonadError.runIO⟩

instance : MonadLift (LogT IO) BuildIO where
  monadLift x := fun meths => liftM (n := BuildIO) (x.run meths.lift) meths

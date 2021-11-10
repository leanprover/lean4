/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Async

namespace Lake

-- # Tasks

instance : Monad Task where
  map := Task.map
  pure := Task.pure
  bind := Task.bind

abbrev ETask ε := ExceptT ε Task

-- # EIO Tasks

def EIOTask ε := ETask ε
instance : Monad (EIOTask ε) := inferInstanceAs <| Monad (ETask ε)

namespace EIOTask

def spawn (act : EIO ε α) (prio := Task.Priority.dedicated) : EIO ε (EIOTask ε α) :=
  EIO.asTask act prio

instance : Async (EIO ε) (EIOTask ε) := ⟨spawn⟩

def await (self : EIOTask ε α) : EIO ε α := do
  liftExcept (← IO.wait self)

instance : Await (EIOTask ε) (EIO ε) := ⟨await⟩

def mapAsync (f : α → EIO ε β) (self : EIOTask ε α) (prio := Task.Priority.dedicated) : EIO ε (EIOTask ε β) :=
  EIO.mapTask (fun x => liftExcept x >>= f) self prio

instance : MapAsync (EIO ε) (EIOTask ε) := ⟨mapAsync⟩

def bindAsync (self : EIOTask ε α) (f : α → EIO ε (EIOTask ε β)) (prio := Task.Priority.dedicated) : EIO ε (EIOTask ε β) :=
  EIO.bindTask self (fun x => liftExcept x >>= f) prio

instance : BindAsync (EIO ε) (EIOTask ε) := ⟨bindAsync⟩

def seqLeftAsync (self : EIOTask ε α) (act : EIO ε β) (prio := Task.Priority.dedicated) : EIO ε (EIOTask ε α) :=
  self.mapAsync (fun a => do discard act; pure a) prio

instance : SeqLeftAsync (EIO ε) (EIOTask ε) := ⟨seqLeftAsync⟩

def seqRightAsync (self : EIOTask ε α) (act : EIO ε β) (prio := Task.Priority.dedicated) : EIO ε (EIOTask ε β) :=
  self.mapAsync (fun _ => act) prio

instance : SeqRightAsync (EIO ε) (EIOTask ε) := ⟨seqRightAsync⟩

end EIOTask

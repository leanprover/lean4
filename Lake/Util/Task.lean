/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Async
import Lake.Util.OptionIO

namespace Lake

-- # Tasks

instance : Monad Task where
  map := Task.map
  pure := Task.pure
  bind := Task.bind

abbrev ETask ε := ExceptT ε Task
abbrev OptionTask := OptionT Task

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

-- # OptionIO Tasks

def OptionIOTask ε := OptionTask ε
instance : Monad OptionIOTask := inferInstanceAs <| Monad OptionTask

def liftOption [Alternative m] : Option α → m α
| some a => pure a
| none => failure

namespace OptionIOTask

def spawn (act : OptionIO α) (prio := Task.Priority.dedicated) : OptionIO (OptionIOTask α) :=
  act.toBaseIO.asTask prio

instance : Async OptionIO OptionIOTask := ⟨spawn⟩

def await (self : OptionIOTask α) : OptionIO α := do
  liftOption (← IO.wait self)

instance : Await OptionIOTask OptionIO := ⟨await⟩

def mapAsync (f : α → OptionIO β) (self : OptionIOTask α) (prio := Task.Priority.dedicated) : OptionIO (OptionIOTask β) :=
  BaseIO.mapTask (fun x => match x with | some a => f a |>.toBaseIO | none => pure none) self prio

instance : MapAsync OptionIO OptionIOTask := ⟨mapAsync⟩

def bindAsync (self : OptionIOTask α) (f : α → OptionIO (OptionIOTask β)) (prio := Task.Priority.dedicated) : OptionIO (OptionIOTask β) :=
  BaseIO.bindTask self (fun x => match x with | some a => f a |>.catchFailure (fun _ => pure <| Task.pure none) | none => pure none) prio

instance : BindAsync OptionIO OptionIOTask := ⟨bindAsync⟩

def seqLeftAsync (self : OptionIOTask α) (act : OptionIO β) (prio := Task.Priority.dedicated) : OptionIO (OptionIOTask α) :=
  self.mapAsync (fun a => do discard act; pure a) prio

instance : SeqLeftAsync OptionIO OptionIOTask := ⟨seqLeftAsync⟩

def seqRightAsync (self : OptionIOTask α) (act : OptionIO β) (prio := Task.Priority.dedicated) : OptionIO (OptionIOTask β) :=
  self.mapAsync (fun _ => act) prio

instance : SeqRightAsync OptionIO OptionIOTask := ⟨seqRightAsync⟩

end OptionIOTask

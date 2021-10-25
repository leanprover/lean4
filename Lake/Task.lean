/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Async

namespace Lake

-- # Tasks

instance : Monad Task where
  map := Task.map
  pure := Task.pure
  bind := Task.bind

abbrev ETask ε α := ExceptT ε Task α

-- # IO Tasks

def IOTask := ETask IO.Error
instance : Monad IOTask := inferInstanceAs <| Monad (ETask IO.Error)

namespace IOTask

def spawn (act : IO α) (prio := Task.Priority.dedicated) : IO (IOTask α) :=
  IO.asTask act prio

instance : Async IO IOTask := ⟨spawn⟩

def await (self : IOTask α) : IO α := do
  match (← IO.wait self) with
  | Except.ok a    => pure a
  | Except.error e => throw e

instance : Await IOTask IO := ⟨await⟩

def mapAsync (f : α → IO β) (self : IOTask α) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.mapTask (fun | Except.ok a => f a | Except.error e => throw e) self prio

instance : MapAsync IO IOTask := ⟨mapAsync⟩

def bindAsync (self : IOTask α) (f : α → IO (IOTask β)) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.bindTask self (fun | Except.ok a => f a | Except.error e => throw e) prio

instance : BindAsync IO IOTask := ⟨bindAsync⟩

def seqLeftAsync (self : IOTask α) (act : IO β) (prio := Task.Priority.dedicated) : IO (IOTask α) :=
  IO.mapTask (fun | Except.ok a => pure a <* act | Except.error e => throw e) self prio

instance : SeqLeftAsync IO IOTask := ⟨seqLeftAsync⟩

def seqRightAsync (self : IOTask α) (act : IO β) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.mapTask (fun | Except.ok a => pure a *> act | Except.error e => throw e) self prio

instance : SeqRightAsync IO IOTask := ⟨seqRightAsync⟩

end IOTask

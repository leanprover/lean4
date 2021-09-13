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

def IOTask α := ETask IO.Error α
instance : Monad IOTask := inferInstanceAs <| Monad (ETask IO.Error)

namespace IOTask

def spawn (act : IO α) (prio := Task.Priority.dedicated) : IO (IOTask α) :=
  IO.asTask act prio

instance : Async IO IOTask := ⟨spawn⟩

def await (self : IOTask α) : IO α := do
  IO.ofExcept (← IO.wait self)

instance : Await IOTask IO := ⟨await⟩

def mapAsync (f : α → IO β) (self : IOTask α) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.mapTask (fun x => do let x ← IO.ofExcept x; f x) self prio

instance : MapAsync IO IOTask := ⟨mapAsync⟩

def bindAsync (self : IOTask α) (f : α → IO (IOTask β)) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.bindTask self (fun x => do let x ← IO.ofExcept x; f x)  prio

instance : BindAsync IO IOTask := ⟨bindAsync⟩

def seqLeftAsync (self : IOTask α) (act : IO β) (prio := Task.Priority.dedicated) : IO (IOTask α) :=
  IO.mapTask (fun x => IO.ofExcept x <* act) self prio

instance : SeqLeftAsync IO IOTask := ⟨seqLeftAsync⟩

def seqRightAsync (self : IOTask α) (act : IO β) (prio := Task.Priority.dedicated) : IO (IOTask β) :=
  IO.mapTask (fun x => IO.ofExcept x *> act) self prio

instance : SeqRightAsync IO IOTask := ⟨seqRightAsync⟩
instance : HAndThen (IOTask α) (IO β) (IO (IOTask β)) :=
  ⟨fun x y => seqRightAsync x (y ())⟩

end IOTask

instance : HAndThen (List (IOTask α)) (IO β) (IO (IOTask β)) :=
  ⟨fun x y => afterTaskList x (y ())⟩

instance : HAndThen (Array (IOTask α)) (IO β) (IO (IOTask β)) :=
  ⟨fun x y => afterTaskArray x (y ())⟩

structure Loop where

@[inline]
partial def Loop.forIn {β : Type u} {m : Type u → Type v} [Monad m] (loop : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  loop init

syntax "while " termBeforeDo "do" doSeq : doElem
syntax "repeat " doSeq "until" term : doElem

macro_rules
  | `(doElem| while $cond do $seq) =>
    `(doElem|
      for _ in Loop.mk do
        if $cond then
          $seq
        else
          break)

macro_rules
  | `(doElem| repeat $seq until $cond) =>
    `(doElem|
      for i in Loop.mk do
        do $seq
        if $cond then break)

def test1 : IO Unit := do
  let mut i := 0
  while i < 10 do
    println! "{i}"
    i := i + 1
  println! "test1 done {i}"

#eval test1

def test2 : IO Unit := do
  let mut i := 0
  repeat
    println! "{i}"
    i := i + 1
  until i >= 10
  println! "test2 done {i}"

#eval test2

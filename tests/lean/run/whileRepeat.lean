structure Loop where

@[inline]
partial def Loop.forIn {β : Type u} {m : Type u → Type v} [Monad m] (loop : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  loop init

instance : ForIn m Loop Unit where
  forIn := Loop.forIn

syntax "repeat " doSeq : doElem

macro_rules
  | `(doElem| repeat $seq) => `(doElem| for _ in Loop.mk do $seq)

syntax "while " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $cond do $seq) =>
    `(doElem| repeat if $cond then $seq else break)

def test1 : IO Unit := do
  let mut i := 0
  while i < 10 do
    println! "{i}"
    i := i + 1
  println! "test1 done {i}"

#eval test1

syntax "repeat " doSeq " until " term : doElem

macro_rules
  | `(doElem| repeat $seq until $cond) =>
    `(doElem| repeat do $seq; if $cond then break)

def test2 : IO Unit := do
  let mut i := 0
  repeat
    println! "{i}"
    i := i + 1
  until i >= 10
  println! "test2 done {i}"

#eval test2

def test3 : IO Unit := do
  let mut i := 0
  repeat
    println! "{i}"
    if i > 10 && i % 3 == 0 then break
    i := i + 1
  println! "test3 done {i}"

#eval test3

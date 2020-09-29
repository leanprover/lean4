new_frontend

inductive ForIn.Step.{u} (α : Type u)
| done  : α → Step α
| yield : α → Step α

@[inline] def List.forIn {α β m} [Monad m] (as : List α) (init : β) (f : α → β → m (ForIn.Step β)) : m β :=
let rec @[specialize] loop
  | [], b    => pure b
  | a::as, b => do
    let s ← f a b
    (match s with
    | ForIn.Step.done b     => pure b
    | ForIn.Step.yield b => loop as b)
loop as init

def tst1 : IO Nat :=
[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14].forIn 0 fun a b =>
  if a % 2 == 0 then do
    IO.println (">> " ++ toString a ++ " " ++ toString b)
    (if b > 20 then return ForIn.Step.done b
     else return ForIn.Step.yield (a+b))
  else
    return ForIn.Step.yield b

#eval tst1

structure Range :=
(lower upper : Nat)

def Range.forIn {β m} [Monad m] (range : Range) (init : β) (f : Nat → β → m (ForIn.Step β)) : m β :=
let base := range.lower + range.upper - 2
let rec @[specialize] loop
  | 0,   b => pure b
  | i+1, b =>
    let j := base - i
    if j >= range.upper then return b
    else do
      let s ← f j b
      (match s with
      | ForIn.Step.done b     => return b
      | ForIn.Step.yield b => loop i b)
loop (range.upper - 1) init

@[inline] def range (a : Nat) (b : Option Nat := none) : Range :=
match b with
| none      => ⟨0, a⟩
| some b    => ⟨a, b⟩

instance : HasOfNat (Option Nat) :=
⟨fun n => some n⟩

def tst3 : IO Nat :=
(range 5 10).forIn 0 fun i s => do
  IO.println (">> " ++ toString i)
  return ForIn.Step.yield (s+i)

#eval tst3

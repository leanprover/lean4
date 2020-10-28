

def tst1 : IO Nat :=
[1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 14].forIn 0 fun a b =>
  if a % 2 == 0 then do
    IO.println (">> " ++ toString a ++ " " ++ toString b)
    (if b > 20 then pure $ ForInStep.done b
     else pure $ ForInStep.yield (a+b))
  else
    pure $ ForInStep.yield b

#eval tst1

structure Range :=
(lower upper : Nat)

def Range.forIn {β m} [Monad m] (range : Range) (init : β) (f : Nat → β → m (ForInStep β)) : m β :=
let base := range.lower + range.upper - 2
let rec @[specialize] loop
  | 0,   b => pure b
  | i+1, b =>
    let j := base - i
    if j >= range.upper then pure b
    else do
      let s ← f j b
      (match s with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i b)
loop (range.upper - 1) init

@[inline] def range (a : Nat) (b : Option Nat := none) : Range :=
match b with
| none      => ⟨0, a⟩
| some b    => ⟨a, b⟩

instance : OfNat (Option Nat) :=
⟨fun n => some n⟩

def tst3 : IO Nat :=
(range 5 10).forIn 0 fun i s => do
  IO.println (">> " ++ toString i)
  pure $ ForInStep.yield (s+i)

#eval tst3

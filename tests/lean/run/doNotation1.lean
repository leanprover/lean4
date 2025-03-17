open Lean

def f : IO Nat :=
pure 0

def g (x : Nat) : IO Nat :=
pure (x + 1)

def g1 {α : Type} (x : α) : IO (α × α) :=
pure (x, x)

def g2 (p : Nat × Nat) : Nat :=
p.1

-- set_option trace.Elab.definition true

def h (x : Nat) : StateT Nat IO Nat := do
let s ← get
let a ← f       -- liftM inserted here
let b ← g1 1    -- liftM inserted here
let x := g2 b
IO.println b
pure (s+a)

def myPrint {α} [ToString α] (a : α) : IO Unit :=
IO.println s!">> {a}"

def h₂ (x : Nat) : StateT Nat IO Nat := do
let a ← h 1;        -- liftM inserted here
IO.println x
let b ← g1 a        -- liftM inserted here
if a > 100 then throw $ IO.userError "Error"
myPrint b.1     -- liftM inserted here
pure (a + 1)

def h₃ (x : Nat) : StateT Nat IO Nat := do
let m1 := do    -- Type inferred from application below
  discard <| g x           -- liftM inserted here
  IO.println 1
let m2 (y : Nat) := do   -- Type inferred from application below
  discard <| h (x+y)       -- liftM inserted here
  myPrint y     -- liftM inserted here
let a ← h 1        -- liftM inserted here
IO.println x
let b ← g1 a;       -- liftM inserted here
if a > 100 then throw $ IO.userError "Error"
myPrint b.1    -- liftM inserted here
m1
m2 a
pure 1

def tst0 : IO Unit := do
let a ← f
let x := a + 1
IO.println "hello"
IO.println x

def tst1 : IO Unit := do
let a ← f;
let x := a + 1;
IO.println "hello";
IO.println x;

def tst2 : IO Unit := do
let x := ← g $ (←f) + (←f);
IO.println "hello";
IO.println x

def tst3 : IO Unit := do
if (← g 1) > 0 then
  IO.println "gt"
else
  let x ← f;
  let y ← g x;
  IO.println y

def pred (x : Nat) : IO Bool := do
return (← g x) > 0

def tst4 (x : Nat) : IO Unit := do
if ← pred x then
  IO.println "is true"
else
  IO.println "is false"

def pred2 (x : Nat) : IO Bool := do
return x > 0

def tst5 (x : Nat) : IO (Option Nat) :=
if x > 10 then pure x else pure none

def tst6 (x : Nat) : StateT Nat IO (Option Nat) :=
if x > 10 then g x else pure none

syntax:max (name := doHash) "#" : term

partial def expandHash : Syntax → StateT Bool MacroM Syntax
| Syntax.node i k args =>
  if k == `doHash then do set true; `(←MonadState.get)
  else do
    let args ← args.mapM expandHash;
    pure $ Syntax.node i k args;
| stx => pure stx

@[macro Lean.Parser.Term.do] def expandDo : Macro :=
fun stx => do
  let (stx, expanded) ← expandHash stx false;
  if expanded then pure stx
  else Macro.throwUnsupported


def tst7 : StateT (Nat × Nat) IO Unit := do
if #.1 == 0 then
  IO.println "first field is zero"
else
  IO.println "first field is not zero"

/-- info: tst7 : StateT (Nat × Nat) IO Unit -/
#guard_msgs in
#check tst7

/--
info: first field is zero
---
info: ((), 0, 2)
-/
#guard_msgs in
#eval tst7.run (0, 2)

def f1 (x : Nat) : StateT Nat IO Nat := do
IO.println "hello"
let mut z := x
let mut y := x
modify (· + 10)
if x > 0 then
  y := 3*y
  z := z + (← get) + (← get)
if x < (← get) then
  IO.println s!">> {y}"
  return y
else
  IO.println s!"++ {z}"
  return y+z

def f1Test : IO Unit := do
unless (← f1 30 |>.run' 0) == 140 do
  throw $ IO.userError $ "error"
unless (← f1 5 |>.run' 0) == 15 do
  throw $ IO.userError $ "error"

/--
info: hello
++ 50
hello
>> 15
-/
#guard_msgs in
#eval f1Test

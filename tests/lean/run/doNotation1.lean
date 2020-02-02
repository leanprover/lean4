open Lean

partial def expandHash : Syntax → StateT Bool MacroM Syntax
| Syntax.node k args =>
  if k == `doHash then do set true; `((^MonadState.get))
  else do
    args ← args.mapM expandHash;
    pure $ Syntax.node k args
| stx => pure stx

@[macro Lean.Parser.Term.do] def expandDo : Macro :=
fun stx => do
  (stx, expanded) ← expandHash stx false;
  if expanded then pure stx
  else Macro.throwUnsupported

new_frontend

def f : IO Nat :=
pure 0

def g (x : Nat) : IO Nat :=
pure (x + 1)

def g1 {α : Type} (x : α) : IO (α × α) :=
pure (x, x)

def g2 (p : Nat × Nat) : Nat :=
p.1

set_option trace.Elab.definition true

def h (x : Nat) : StateT Nat IO Nat := do
s ← get;
a ← f;            -- liftM inserted here
b ← g1 (1:Nat);   -- liftM inserted here
let x := g2 b;
IO.println b;
pure (s+a)

def myPrint {α} [HasToString α] (a : α) : IO Unit :=
IO.println (">> " ++ toString a)

def h₂ (x : Nat) : ExceptT String (StateT Nat IO) Nat := do
a ← h 1;        -- liftM inserted here
IO.println x;
b ← g1 a;       -- liftM inserted here
when (a > 100) $ throw "Error";
myPrint b.1;    -- liftM inserted here
pure (a + 1)

def tst1 : IO Unit := do
a ← f;
let x := a + 1;
IO.println "hello";
IO.println x

def tst2 : IO Unit := do
let x := (^g $ (^f) + (^f));
IO.println "hello";
IO.println x

def tst3 : IO Unit := do
if (^g 1) > 0 then
  IO.println "gt"
else do
  x ← f;
  y ← g x;
  IO.println y

syntax [doHash] "#":max : term

def tst4 : StateT (Nat × Nat) IO Unit := do
if #.1 == 0 then
  IO.println "first field is zero"
else
  IO.println "first field is not zero"

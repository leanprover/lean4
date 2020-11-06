theorem zeroLtOfLt : {a b : Nat} → a < b → 0 < b
| 0,   _, h => h
| a+1, b, h =>
  have a < b from Nat.ltTrans (Nat.ltSuccSelf _) h
  zeroLtOfLt this

def fold {m α β} [Monad m] (as : Array α) (b : β) (f : α → β → m β) : m β := do
let rec loop : (i : Nat) → i ≤ as.size → β → m β
  | 0,   h, b => b
  | i+1, h, b => do
    have h' : i < as.size          from Nat.ltOfLtOfLe (Nat.ltSuccSelf i) h
    have as.size - 1 < as.size     from Nat.subLt (zeroLtOfLt h') (decide! : 0 < 1)
    have as.size - 1 - i < as.size from Nat.ltOfLeOfLt (Nat.subLe (as.size - 1) i) this
    let b ← f (as.get ⟨as.size - 1 - i, this⟩) b
    loop i (Nat.leOfLt h') b
loop as.size (Nat.leRefl _) b

#eval Id.run $ fold #[1, 2, 3, 4] 0 (pure $ · + ·)

theorem ex : (Id.run $ fold #[1, 2, 3, 4] 0 (pure $ · + ·)) = 10 :=
rfl

def fold2 {m α β} [Monad m] (as : Array α) (b : β) (f : α → β → m β) : m β :=
let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
  match i, h with
  | 0,   h => return b
  | i+1, h =>
    have h' : i < as.size          from Nat.ltOfLtOfLe (Nat.ltSuccSelf i) h
    have as.size - 1 < as.size     from Nat.subLt (zeroLtOfLt h') (decide! : 0 < 1)
    have as.size - 1 - i < as.size from Nat.ltOfLeOfLt (Nat.subLe (as.size - 1) i) this
    let b ← f (as.get ⟨as.size - 1 - i, this⟩) b
    loop i (Nat.leOfLt h') b
loop as.size (Nat.leRefl _) b

def f (x : Nat) (ref : IO.Ref Nat) : IO Nat := do
let x := x
if x == 0 then
  x ← ref.get
IO.println x
return x + 1

def fTest : IO Unit := do
unless (← f 0 (← IO.mkRef 10)) == 11 do throw $ IO.userError "unexpected"
unless (← f 1 (← IO.mkRef 10)) == 2 do throw $ IO.userError "unexpected"

set_option relaxedReassignments true in
def g (x y : Nat) (ref : IO.Ref (Nat × Nat)) : IO (Nat × Nat) := do
if x == 0 then
  (x, y) ← ref.get
IO.println ("x: " ++ toString x ++ ", y: " ++ toString y)
return (x, y)

def gTest : IO Unit := do
unless (← g 2 1 (← IO.mkRef (10, 20))) == (2, 1)   do throw $ IO.userError "unexpected"
unless (← g 0 1 (← IO.mkRef (10, 20))) == (10, 20) do throw $ IO.userError "unexpected"
return ()

#eval gTest

macro "ret!" x:term : doElem => `(return $x)

set_option relaxedReassignments true in
def f1 (x : Nat) : Nat := do
if x == 0 then
  ret! 100
x := x + 1
ret! x

theorem ex1 : f1 0 = 100 := rfl
theorem ex2 : f1 1 = 2 := rfl
theorem ex3 : f1 3 = 4 := rfl

syntax "inc!" ident : doElem

macro_rules
| `(doElem| inc! $x) => `(doElem| $x:ident := $x + 1)

set_option relaxedReassignments true in
def f2 (x : Nat) : Nat := do
inc! x
ret! x

theorem ex4 : f2 0 = 1 := rfl
theorem ex5 : f2 3 = 4 := rfl

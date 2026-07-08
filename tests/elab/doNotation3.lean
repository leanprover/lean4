theorem zero_lt_of_lt : {a b : Nat} → a < b → 0 < b
| 0,   _, h => h
| a+1, b, h =>
  have : a < b := Nat.lt_trans (Nat.lt_succ_self _) h
  zero_lt_of_lt this

def fold {m α β} [Monad m] (as : Array α) (b : β) (f : α → β → m β) : m β := do
let rec loop : (i : Nat) → i ≤ as.size → β → m β
  | 0,   h, b => pure b
  | i+1, h, b => do
    have h' : i < as.size          := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
    have : as.size - 1 < as.size     := Nat.sub_lt (zero_lt_of_lt h') (by decide)
    have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
    let b ← f as[as.size - 1 - i] b
    loop i (Nat.le_of_lt h') b
loop as.size (Nat.le_refl _) b

#guard (Id.run $ fold #[1, 2, 3, 4] 0 (pure $ · + ·)) == 10

theorem ex : (Id.run $ fold #[1, 2, 3, 4] 0 (pure $ · + ·)) = 10 :=
rfl

def fold2 {m α β} [Monad m] (as : Array α) (b : β) (f : α → β → m β) : m β :=
let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
  match i, h with
  | 0,   h => return b
  | i+1, h =>
    have h' : i < as.size          := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
    have : as.size - 1 < as.size     := Nat.sub_lt (zero_lt_of_lt h') (by decide)
    have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
    let b ← f as[as.size - 1 - i] b
    loop i (Nat.le_of_lt h') b
loop as.size (Nat.le_refl _) b

def f (x : Nat) (ref : IO.Ref Nat) : IO Nat := do
let mut x := x
if x == 0 then
  x ← ref.get
IO.println x
return x + 1

def fTest : IO Unit := do
unless (← f 0 (← IO.mkRef 10)) == 11 do throw $ IO.userError "unexpected"
unless (← f 1 (← IO.mkRef 10)) == 2 do throw $ IO.userError "unexpected"

def g (x y : Nat) (ref : IO.Ref (Nat × Nat)) : IO (Nat × Nat) := do
  let mut (x, y) := (x, y)
  if x == 0 then
    (x, y) ← ref.get
  IO.println ("x: " ++ toString x ++ ", y: " ++ toString y)
  return (x, y)

def gTest : IO Unit := do
unless (← g 2 1 (← IO.mkRef (10, 20))) == (2, 1)   do throw $ IO.userError "unexpected"
unless (← g 0 1 (← IO.mkRef (10, 20))) == (10, 20) do throw $ IO.userError "unexpected"
return ()

/--
info: x: 2, y: 1
x: 10, y: 20
-/
#guard_msgs in
#eval gTest

macro "ret!" x:term : doElem => `(doElem| return $x)

def f1 (x : Nat) : Nat := Id.run <| do
  let mut x := x
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

def f2 (x : Nat) : Nat := Id.run <| do
  let mut x := x
  inc! x
  ret! x

theorem ex4 : f2 0 = 1 := rfl
theorem ex5 : f2 3 = 4 := rfl

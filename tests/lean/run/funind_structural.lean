/-!
This module tests functional induction principles on *structurally* recursive functions.
-/

def fib : Nat → Nat
  | 0 | 1 => 0
  | n+2 => fib n + fib (n+1)

derive_functional_induction fib
/--
info: fib.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive n → motive (n + 1) → motive (Nat.succ (Nat.succ n))) : ∀ (a : Nat), motive a
-/
#guard_msgs in
#check fib.induct


def binary : Nat → Nat → Nat
  | 0, acc | 1, acc => 1 + acc
  | n+2, acc => binary n (binary (n+1) acc)

derive_functional_induction binary
/--
info: binary.induct (motive : Nat → Nat → Prop) (case1 : ∀ (acc : Nat), motive 0 acc) (case2 : ∀ (acc : Nat), motive 1 acc)
  (case3 : ∀ (n acc : Nat), motive (n + 1) acc → motive n (binary (n + 1) acc) → motive (Nat.succ (Nat.succ n)) acc) :
  ∀ (a a_1 : Nat), motive a a_1
-/
#guard_msgs in
#check binary.induct


-- Different parameter order
def binary' : Bool → Nat → Bool
  | acc, 0 | acc , 1 => not acc
  | acc, n+2 => binary' (binary' acc (n+1)) n

derive_functional_induction binary'
/--
info: binary'.induct (motive : Bool → Nat → Prop) (case1 : ∀ (acc : Bool), motive acc 0)
  (case2 : ∀ (acc : Bool), motive acc 1)
  (case3 :
    ∀ (acc : Bool) (n : Nat),
      motive acc (n + 1) → motive (binary' acc (n + 1)) n → motive acc (Nat.succ (Nat.succ n))) :
  ∀ (a : Bool) (a_1 : Nat), motive a a_1
-/
#guard_msgs in
#check binary'.induct

def zip {α β} : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (x, y) :: zip xs ys

derive_functional_induction zip
/--
info: zip.induct.{u_1, u_2} {α : Type u_1} {β : Type u_2} (motive : List α → List β → Prop)
  (case1 : ∀ (x : List β), motive [] x) (case2 : ∀ (x : List α), (x = [] → False) → motive x [])
  (case3 : ∀ (x : α) (xs : List α) (y : β) (ys : List β), motive xs ys → motive (x :: xs) (y :: ys)) :
  ∀ (a : List α) (a_1 : List β), motive a a_1
-/
#guard_msgs in
#check zip.induct

/-- Lets try ot use it! -/
theorem zip_length {α β} (xs : List α) (ys : List β) :
    (zip xs ys).length = xs.length.min ys.length := by
  induction xs, ys using zip.induct
  case case1 => simp [zip]
  case case2 => simp [zip]
  case case3 =>
    simp [zip, *]
    simp [Nat.min_def]
    split<;>split<;> omega


-- Just for testing
inductive Finn : Nat → Type where
  | fzero : {n : Nat} → Finn n
  | fsucc : {n : Nat} → Finn n → Finn (n+1)

def Finn.min (x : Bool) {n : Nat} (m : Nat) : Finn n → (f : Finn n) → Finn n
  | fzero, _ => fzero
  | _, fzero => fzero
  | fsucc i, fsucc j => fsucc (Finn.min (not x) (m + 1) i j)

derive_functional_induction Finn.min
/--
info: Finn.min.induct (motive : Bool → {n : Nat} → Nat → Finn n → Finn n → Prop)
  (case1 : ∀ (x : Bool) (m n : Nat) (x_1 : Finn n), motive x m Finn.fzero x_1)
  (case2 : ∀ (x : Bool) (m n : Nat) (x_1 : Finn n), (x_1 = Finn.fzero → False) → motive x m x_1 Finn.fzero)
  (case3 : ∀ (x : Bool) (m n : Nat) (i j : Finn n), motive (!x) (m + 1) i j → motive x m (Finn.fsucc i) (Finn.fsucc j))
  (x : Bool) {n : Nat} (m : Nat) : ∀ (a f : Finn n), motive x m a f
-/
#guard_msgs in
#check Finn.min.induct

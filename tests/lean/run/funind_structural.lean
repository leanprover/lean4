/-!
This module tests functional induction principles on *structurally* recursive functions.
-/


def fib : Nat → Nat
  | 0 | 1 => 0
  | n+2 => fib n + fib (n+1)

derive_functional_induction fib
/--
info: fib.induct :
  ∀ (a : Nat) (motive : Nat → Prop),
    motive 0 → motive 1 → (∀ (n : Nat), motive n → motive (n + 1) → motive (Nat.succ (Nat.succ n))) → motive a
-/
#guard_msgs in
#check fib.induct


def binary : Nat → Nat → Nat
  | 0, acc | 1, acc => 1 + acc
  | n+2, acc => binary n (binary (n+1) acc)

derive_functional_induction binary
/--
info: binary.induct :
  ∀ (a a_1 : Nat) (motive : Nat → Nat → Prop),
    (∀ (acc : Nat), motive 0 acc) →
      (∀ (acc : Nat), motive 1 acc) →
        (∀ (n acc : Nat), motive (n + 1) acc → motive n (binary (n + 1) acc) → motive (Nat.succ (Nat.succ n)) acc) →
          motive a a_1
-/
#guard_msgs in
#check binary.induct


-- Different parameter order
def binary' : Bool → Nat → Bool
  | acc, 0 | acc , 1 => not acc
  | acc, n+2 => binary' (binary' acc (n+1)) n

derive_functional_induction binary'
/--
info: binary'.induct :
  ∀ (a : Bool) (a_1 : Nat) (motive : Bool → Nat → Prop),
    (∀ (acc : Bool), motive acc 0) →
      (∀ (acc : Bool), motive acc 1) →
        (∀ (acc : Bool) (n : Nat),
            motive acc (n + 1) → motive (binary' acc (n + 1)) n → motive acc (Nat.succ (Nat.succ n))) →
          motive a a_1
-/
#guard_msgs in
#check binary'.induct

def zip {α β} : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | x::xs, y::ys => (x, y) :: zip xs ys

derive_functional_induction zip
/--
info: zip.induct.{u_1, u_2} {α : Type u_1} {β : Type u_2} :
  ∀ (a : List α) (a_1 : List β) (motive : List α → List β → Prop),
    (∀ (x : List β), motive [] x) →
      (∀ (x : List α), (x = [] → False) → motive x []) →
        (∀ (x : α) (xs : List α) (y : β) (ys : List β), motive xs ys → motive (x :: xs) (y :: ys)) → motive a a_1
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
info: Finn.min.induct (x : Bool) {n : Nat} (m : Nat) :
  ∀ (a f : Finn n) (motive : Bool → {n : Nat} → Nat → Finn n → Finn n → Prop),
    (∀ (x : Bool) (m n : Nat) (x_1 : Finn n), motive x m Finn.fzero x_1) →
      (∀ (x : Bool) (m n : Nat) (x_1 : Finn n), (x_1 = Finn.fzero → False) → motive x m x_1 Finn.fzero) →
        (∀ (x : Bool) (m n : Nat) (i j : Finn n), motive (!x) (m + 1) i j → motive x m (Finn.fsucc i) (Finn.fsucc j)) →
          motive x m a f
-/
#guard_msgs in
#check Finn.min.induct

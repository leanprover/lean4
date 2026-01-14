set_option warn.sorry false
namespace Test
set_option backward.grind.inferPattern false -- Force new pattern inference procedure

inductive Vector (α : Type) : Nat → Type where
  | nil : Vector α 0
  | cons (x : α) (xs : Vector α n) : Vector α (n + 1)

def Vector.ofList (xs : List α) (h : xs.length = n) : Vector α n :=
  match n, xs with
  | 0, [] => .nil
  | (n + 1), x :: xs => .cons x (.ofList xs (by grind))

def Vector.toList (xs : Vector α n) : List α :=
  match xs with
  | .nil => []
  | .cons x xs => x :: xs.toList

/-- info: length_toList: [@toList #2 #1 #0] -/
#guard_msgs (info) in
@[grind!? ←] theorem Vector.length_toList (xs : Vector α n) : xs.toList.length = n := by sorry

def wrapper (f : Nat → Nat → List α → List α) (h : ∀ n m xs, xs.length = n → (f n m xs).length = m) :
    (n m : Nat) → Vector α n → Vector α m :=
  fun n m xs => Vector.ofList (f n m xs.toList) (by grind) -- apply h; apply Vector.length_toList) -- fails here: (by grind)

/--
warning: found discrepancy between old and new `grind` pattern inference procedures, old:
  [@List.length #2 (@toList _ #1 #0)]
new:
  [@toList #2 #1 #0]
-/
#guard_msgs in
set_option backward.grind.checkInferPatternDiscrepancy true in
@[grind! ←] theorem Vector.length_toList' (xs : Vector α n) : xs.toList.length = n := by sorry

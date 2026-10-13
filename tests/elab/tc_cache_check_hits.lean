/-!
Runs representative elaboration with `debug.synthInstance.checkCacheHits`, the differential
validation of type class resolution cache hits: every served entry is recomputed from scratch
and compared. A panic here means a served result diverged from recomputation, i.e. some
dependency of the entry was not recorded.
-/

set_option debug.synthInstance.checkCacheHits true

class R (α : Type) where
  val : Nat

instance : R Nat := ⟨1⟩
instance : R (List α) := ⟨2⟩
instance [R α] [R β] : R (α × β) := ⟨3⟩

def f (n : Nat) : Nat := R.val Nat + n

example : R.val (List Nat) = 2 := rfl
example : R.val (List Nat) = 2 := rfl
example : R.val (Nat × List Nat) = 3 := rfl
example : R.val (Nat × List Nat) = 3 := rfl

def sumIt (l : List Nat) : Nat := l.foldl (· + ·) 0

example : sumIt [1, 2, 3] = 6 := by simp [sumIt]
example : sumIt [1, 2, 3] = 6 := by simp [sumIt]

structure Wrap where
  out : Nat

instance : R Wrap := ⟨4⟩

example (w : Wrap) : R.val Wrap + w.out = 4 + w.out := rfl

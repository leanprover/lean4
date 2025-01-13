/-!
Example for the lean together demo
-/

#exit

variable (f : α → Option α)

partial def whileSome (x : α) : α :=
  match f x with
  | none => x
  | some x' => whileSome x'

/-- info: 10 -/
#guard_msgs in
#eval whileSome (fun x => do guard (x < 10); pure (x+1)) 1

theorem whileSome_none : whileSome (fun _ => none) x = x := by
  simp [whileSome]

section

example : whileSome (fun x => do guard (x < 10); pure (x+1)) 1 = 10 := by
  -- simp [whileSome]
  repeat (rw [whileSome]; simp [guard, failure])
  done

section

--example : whileSome (fun x => pure x) 1 = ??

section

/-- Soundness is not in danger -/
def findNat (f : Nat → Option α) (i : Nat) : α :=
  match f i with
  | none => findNat f (i+1)
  | some x' => x'
partial_fixpoint

section

/-- Within Option monad, we can prove partial correctness -/

def whileSome' (x : α) : Option α :=
  match f x with
  | none => x
  | some x' => whileSome' x'
partial_fixpoint

theorem whileSome'_correct : whileSome' f x = some r → f r = none := by
  apply whileSome'.partial_correctness
  intros whileSome ih x r hyp
  split at hyp
  · simp_all
  · apply ih _ _ hyp

section


/-! Essentially any monadic function works -- useful for program verification -/

def ack : (n m : Nat) → Option Nat
  | 0,   y   => some (y+1)
  | x+1, 0   => ack x 1
  | x+1, y+1 => do ack x (← ack (x+1) y)
partial_fixpoint

/-! Even nested recursion-/

structure Tree where cs : List Tree

def Tree.rev (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.mapM (Tree.rev ·))
partial_fixpoint

def Tree.rev' (t : Tree) : Option Tree := do
  let mut cs := []
  for c in t.cs do
    cs := (← c.rev') :: cs
  return Tree.mk cs
partial_fixpoint

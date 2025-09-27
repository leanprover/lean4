structure S where
  fn1 : Nat
  value : Bool
  name : String

def f (s : S) : Nat := by
  refine s.
         --^ completion

def g (s : S) : Nat := by
  match s.
        --^ completion

theorem ex (x : Nat) : 0 + x = x := by
  match x with
--^ $/lean/plainGoal
  | 0 => done
       --^ $/lean/plainGoal

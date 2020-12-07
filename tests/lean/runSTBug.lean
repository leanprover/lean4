import Lean

open Lean

def f (xs : List Nat) (delta : Nat) : List Nat :=
  runST (fun ω => visit xs |>.run)
where
  visit {ω} : List Nat → MonadCacheT Nat Nat (ST ω) (List Nat)
    | []    => []
    | a::as => do
      let b ← checkCache a fun _ => return a + delta
      return b :: (← visit as)

def tst (xs : List Nat) : IO Unit := do
  IO.println (f xs 10)
  IO.println (f xs 20)
  IO.println (f xs 30)

#eval tst [1, 2, 3, 1, 2]

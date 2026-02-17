import Baseline
import Lean
import Driver

open Lean Meta Sym

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ s post, post () s → Exec s (loop n) post

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingSym ``Goal [``loop, ``step] solve
  [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
  -- [1000]

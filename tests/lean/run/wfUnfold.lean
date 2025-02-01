def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
decreasing_by all_goals sorry

/--
error: tactic 'fail' failed
⊢ fib 8 + fib (8 + 1) = 55
-/
#guard_msgs in
example : fib 10 = 55 := by
  unfold fib
  fail

def ack : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ack n 1
  | n+1, m+1 => ack n (ack (n+1) m)
decreasing_by all_goals sorry

/--
error: tactic 'fail' failed
⊢ ack 1 (ack (1 + 1) 1) = 7
-/
#guard_msgs in
example : ack 2 2 = 7 := by
  unfold ack
  fail

-- This checks that we can unfold definitions in the prelude
/--
error: tactic 'fail' failed
α : Type u_1
as : Array α
i : Nat
j : Fin as.size
⊢ (if i < ↑j then
        let j' := ⟨↑j - 1, ⋯⟩;
        let as_1 := as.swap ↑j' ↑j ⋯ ⋯;
        insertIdx.loop i as_1 ⟨↑j', ⋯⟩
      else as).size =
    as.size
-/
#guard_msgs in
@[simp] private theorem Array.size_insertIdx_loop (as : Array α) (i : Nat) (j : Fin as.size) :
    (insertIdx.loop i as j).size = as.size := by
  unfold insertIdx.loop
  fail

module
opaque f : Nat → Nat
opaque op : Nat → Nat → Nat
@[grind] theorem op_comm : op x y = op y x := sorry
@[grind] theorem op_assoc : op (op x y) z = op x (op y z) := sorry

syntax "gen! " num : term

macro_rules
  | `(gen! 0) => `(f 0)
  | `(gen! $n:num) => `(op (f $n) (gen! $(Lean.quote (n.getNat - 1))))

-- This test has been commented out as it is nondeterministic:
-- sometimes it fails with a timeout at `whnf` rather than `isDefEq`.
-- /--
-- trace: [grind.issues] (deterministic) timeout at `isDefEq`, maximum number of heartbeats (5000) has been reached
--     Use `set_option maxHeartbeats <num>` to set the limit.
--     ⏎
--     Additional diagnostic information may be available using the `set_option diagnostics true` command.
-- -/
-- #guard_msgs (trace, drop error) in
-- set_option trace.grind.issues true in
-- set_option maxHeartbeats 5000 in
-- example : gen! 10 = 0 ∧ True := by
--   set_option trace.Meta.debug true in
--   grind (instances := 10000)

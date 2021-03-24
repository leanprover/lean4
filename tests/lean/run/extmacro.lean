macro "ext_tactic" t:tactic "=>" newT:tactic : command => `(macro_rules | `($t) => `($newT))

syntax "trivial'" : tactic

ext_tactic trivial' => apply Eq.refl

theorem tst1 (x : Nat) : x = x :=
by trivial'

-- theorem tst2 (x y : Nat) (h : x = y) : x = y :=
-- by trivial' -- fail as expected

ext_tactic trivial' => assumption

theorem tst1b (x : Nat) : x = x :=
by trivial' -- still works

theorem tst2 (x y : Nat) (h : x = y) : x = y :=
by trivial' -- works too

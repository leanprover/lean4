new_frontend

macro ext_tactic t:tactic "=>" newT:tactic : command => `(macro_rules | `($t) => `($newT))

syntax "trivial" : tactic

ext_tactic trivial => apply Eq.refl

theorem tst1 (x : Nat) : x = x :=
begin trivial end

-- theorem tst2 (x y : Nat) (h : x = y) : x = y :=
-- begin trivial end -- fail as expected

ext_tactic trivial => assumption

theorem tst1b (x : Nat) : x = x :=
begin trivial end -- still works

theorem tst2 (x y : Nat) (h : x = y) : x = y :=
begin trivial end -- works too

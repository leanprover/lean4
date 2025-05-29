-- In nightly-2025-05-27 this leads to grind internal error "trying to assert equality c = (c.fst, c.snd) with proof Eq.refl c which has type c = c which is not definitionally equal with `reducible` transparency setting"

set_option grind.warning false
set_option grind.debug true


def α : Type := Unit × Unit

def p (_ : α) : Prop := False
/--
error: tactic 'grind.cases' failed, (non-recursive) inductive type expected at c
  α
case grind
c : α
h : p c
⊢ False
-/
#guard_msgs in
example : p c → False := by grind

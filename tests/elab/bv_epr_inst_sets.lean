import Std.Tactic.BVDecide

/-!
Tests for the Z3 style instantiation sets and projections of the EPR MBQI procedure: how literals of
the quantifier bodies shape the classes, their instantiation sets, exceptions and avoid sets, and how
ground terms of new instances enrich the instantiation sets.
-/

section Traces

set_option trace.Meta.Tactic.bv.epr.instSets true

-- Variables of different quantifiers are merged through the predicate positions they share.
/--
trace: [Meta.Tactic.bv.epr.instSets] ✅️ Instantiation set analysis
  [Meta.Tactic.bv.epr.instSets] quantifier 0 variable 0: class 0
  [Meta.Tactic.bv.epr.instSets] quantifier 1 variable 0: class 0
  [Meta.Tactic.bv.epr.instSets] projection p 0: class 0
  [Meta.Tactic.bv.epr.instSets] projection q 0: class 0
  [Meta.Tactic.bv.epr.instSets] class 0: terms [a, b], exceptions [], avoid []
[Meta.Tactic.bv.epr.instSets] ✅️ Instantiation sets
  [Meta.Tactic.bv.epr.instSets] class 0: [a, b]
[Meta.Tactic.bv.epr.instSets] ✅️ Instantiation sets
  [Meta.Tactic.bv.epr.instSets] class 0: [a, b]
[Meta.Tactic.bv.epr.instSets] ✅️ Instantiation sets
  [Meta.Tactic.bv.epr.instSets] class 0: [a, b]
-/
#guard_msgs in
example (α : Type) (a b c : α) (p q : α → Prop) (h1 : ∀ x, p x → q x) (h2 : ∀ x, q x → p b)
    (h3 : p a) (h4 : ¬p b) : False := by
  bv_decide +epr +uf

-- `x = a` in positive position: `a` is an exception and the class is unrestricted.
/--
trace: [Meta.Tactic.bv.epr.instSets] ✅️ Instantiation set analysis
  [Meta.Tactic.bv.epr.instSets] quantifier 0 variable 0: class 0
  [Meta.Tactic.bv.epr.instSets] projection p 0: class 0
  [Meta.Tactic.bv.epr.instSets] class 0: terms [b], exceptions [a], avoid [], full
[Meta.Tactic.bv.epr.instSets] ✅️ Instantiation sets
-/
#guard_msgs in
example (α : Type) (a b : α) (p : α → Prop) (h1 : ∀ x, x = a ∨ p x) (h2 : ¬p b) (h3 : a ≠ b) :
    False := by
  bv_decide +epr +uf

-- `x = y` in positive position puts `x` and `y` into each other's avoid set. The problem is
-- satisfiable and the instance with `y := b` adds `b` to the instantiation set of the next round.
/--
error: The prover found a counterexample, consider the following assignment:
r a = False
a = α₀
s a = False
b = α₀
s b = False
---
trace: [Meta.Tactic.bv.epr.instSets] ✅️ Instantiation set analysis
  [Meta.Tactic.bv.epr.instSets] quantifier 0 variable 0: class 0
  [Meta.Tactic.bv.epr.instSets] quantifier 0 variable 1: class 1
  [Meta.Tactic.bv.epr.instSets] projection r 0: class 0
  [Meta.Tactic.bv.epr.instSets] projection s 0: class 1
  [Meta.Tactic.bv.epr.instSets] class 0: terms [a], exceptions [], avoid [1]
  [Meta.Tactic.bv.epr.instSets] class 1: terms [a], exceptions [], avoid [0]
[Meta.Tactic.bv.epr.instSets] ✅️ Instantiation sets
  [Meta.Tactic.bv.epr.instSets] class 0: [a]
  [Meta.Tactic.bv.epr.instSets] class 1: [a]
[Meta.Tactic.bv.epr.instSets] ✅️ Instantiation sets
  [Meta.Tactic.bv.epr.instSets] class 0: [a]
  [Meta.Tactic.bv.epr.instSets] class 1: [a, b]
-/
#guard_msgs in
example (α : Type) (a b : α) (r s : α → Prop) (h1 : ∀ x y, x = y ∨ r x ∨ s y) (h2 : ¬r a)
    (h3 : ¬s a) : False := by
  bv_decide +epr +uf

end Traces

section Unsat

variable (α : Type) (a b c : α) (p q : α → Prop) (r : α → α → Prop)

example (h1 : ∀ x y, x = y → r x y) (h2 : ¬r b b) : False := by
  bv_decide +epr +uf

example (h1 : ∀ x y, r x y → r y x) (h2 : ∀ x y z, r x y → r y z → r x z) (h3 : r a b)
    (h4 : r b c) (h5 : ¬r c a) : False := by
  bv_decide +epr +uf

example (h1 : ∀ x y, r x y → r y x) (h2 : ∀ x y z, r x y → r y z → r x z) (h3 : r a b)
    (h4 : r b c) (h5 : ¬r c a) : False := by
  bv_decide +epr +uf -eprProjections

end Unsat

section Sat

-- The same satisfiable problem with and without projections.
/--
error: The prover found a counterexample, consider the following assignment:
r a b = True
a = α₀
b = α₁
p c = False
c = α₂
p b = True
r a c = False
-/
#guard_msgs in
example (α : Type) (a b c : α) (p : α → Prop) (r : α → α → Prop) (h1 : ∀ x y, r x y → p y ∨ x = y)
    (h2 : r a b) (h3 : ¬p c) : False := by
  bv_decide +epr +uf

/--
error: The prover found a counterexample, consider the following assignment:
r a b = True
a = α₀
b = α₁
p c = False
c = α₂
r b a = False
p a = False
p b = True
r b c = False
-/
#guard_msgs in
example (α : Type) (a b c : α) (p : α → Prop) (r : α → α → Prop) (h1 : ∀ x y, r x y → p y ∨ x = y)
    (h2 : r a b) (h3 : ¬p c) : False := by
  bv_decide +epr +uf -eprProjections

end Sat

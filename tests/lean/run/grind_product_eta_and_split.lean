module
set_option grind.debug true

def α : Type := Unit × Unit

def p (_ : α) : Prop := False

/--
error: `grind` failed
case grind
c : α
h : p c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] p c
  [eqc] True propositions
    [prop] p c
-/
#guard_msgs in
example : p c → False := by
  grind

example : p c → False := by
  grind [p]


def PosFin (n : Nat) := {x : Nat // 0 < x ∧ x < n}

def f (_ : PosFin n) : Prop := False

/--
error: `grind` failed
case grind
n : Nat
fst : PosFin n
h : f fst
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] f fst
  [eqc] True propositions
    [prop] f fst
-/
#guard_msgs in
example (n : Nat) (fst : PosFin n) (h : f fst) : False := by
  grind

example (n : Nat) (fst : PosFin n) (h : f fst) : False := by
  grind [f]

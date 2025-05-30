set_option grind.warning false
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

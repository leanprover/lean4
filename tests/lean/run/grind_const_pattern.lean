set_option grind.warning false
reset_grind_attrs%

attribute [grind] List.map_append

def a := 10

example : a = 5 + 5 := by
  grind [a]

/--
error: `grind` failed
case grind
h : ¬a = 10
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬a = 10
  [eqc] False propositions
    [prop] a = 10
-/
#guard_msgs (error) in
example : a = 5 + 5 := by
  grind

section
attribute [local grind] a

example : a = 5 + 5 := by
  grind
end

def f (x : Nat) := x + 1

theorem fa : f a = 11 := rfl

example : f a = 10 + 1 := by
  grind [fa]

/--
error: `grind` failed
case grind
h : ¬f a = 11
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬f a = 11
  [eqc] False propositions
    [prop] f a = 11
-/
#guard_msgs (error) in
example : f a = 10 + 1 := by
  grind

attribute [grind] fa

example : f a = 10 + 1 := by
  grind

/--
error: `grind` failed
case grind
x : Nat
h : ¬f x = 11
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬f x = 11
  [eqc] False propositions
    [prop] f x = 11
  [ematch] E-matching patterns
    [thm] fa: [f `[a]]
-/
#guard_msgs (error) in
example : f x = 10 + 1 := by
  grind

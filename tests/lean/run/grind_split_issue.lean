variable (d : Nat) in
inductive X : Nat → Prop
  | f {s : Nat} : X s
  | g {s : Nat} : X d → X s

/--
error: `grind` failed
case grind.1
c : Nat
q : X c 0
s : Nat
h✝ : 0 = s
h : HEq ⋯ ⋯
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] X c 0
    [prop] 0 = s
    [prop] HEq ⋯ ⋯
  [eqc] True propositions
    [prop] X c 0
    [prop] X c s
  [eqc] Equivalence classes
    [eqc] {s, 0}
case grind.2
c : Nat
q : X c 0
s : Nat
a✝¹ a✝ : X c c
h✝ : 0 = s
h : HEq ⋯ ⋯
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] X c 0
    [prop] X c c
    [prop] 0 = s
    [prop] HEq ⋯ ⋯
  [eqc] True propositions
    [prop] X c 0
    [prop] X c c
    [prop] X c s
  [eqc] Equivalence classes
    [eqc] {s, 0}
  [issues] Issues
    [issue] this goal was not fully processed due to previous failures, threshold: `(failures := 1)`
-/
#guard_msgs (error) in
example {c : Nat} (q : X c 0) : False := by
  grind [X]

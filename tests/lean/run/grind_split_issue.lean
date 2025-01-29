variable (d : Nat) in
inductive X : Nat → Prop
  | f {s : Nat} : X s
  | g {s : Nat} : X d → X s

/--
error: `grind` failed
case grind.1.1
c : Nat
q : X c 0
s✝ : Nat
h✝² : 0 = s✝
h✝¹ : HEq ⋯ ⋯
s : Nat
h✝ : c = s
h : HEq ⋯ ⋯
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] X c 0
    [prop] X c 0
    [prop] X c c → X c 0
    [prop] X c c
    [prop] 0 = s✝
    [prop] HEq ⋯ ⋯
    [prop] c = s
    [prop] HEq ⋯ ⋯
  [eqc] True propositions
    [prop] X c 0
    [prop] X c c → X c 0
    [prop] X c c
    [prop] X c s✝
    [prop] X c s
  [eqc] Equivalence classes
    [eqc] {c, s}
    [eqc] {s✝, 0}
  [ematch] E-matching patterns
    [thm] X.f: [X #1 #0]
    [thm] X.g: [X #2 #1]
[grind] Issues
  [issue] #2 other goal(s) were not fully processed due to previous failures, threshold: `(failures := 1)`
[grind] Counters
  [thm] E-Matching instances
    [thm] X.f ↦ 2
    [thm] X.g ↦ 2
-/
#guard_msgs (error) in
example {c : Nat} (q : X c 0) : False := by
  grind [X]

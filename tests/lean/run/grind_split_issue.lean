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
h : 0 = s
h_1 : ⋯ ≍ ⋯
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] X c 0
    [prop] 0 = s
    [prop] ⋯ ≍ ⋯
  [eqc] True propositions
    [prop] X c 0
    [prop] X c s
  [eqc] Equivalence classes
    [eqc] {0, s}
  [cases] Case analyses
    [cases] [1/2]: X c 0
      [cases] source: Initial goal
  [cutsat] Assignment satisfying linear constraints
    [assign] c := 2
    [assign] s := 0
-/
#guard_msgs (error) in
example {c : Nat} (q : X c 0) : False := by
  grind -mbtc [cases X]

example {c : Nat} (q : X c 0) : False := by
  fail_if_success grind [cases X]
  sorry

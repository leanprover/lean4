module
opaque f [Inhabited α] : α → α
theorem feq [Inhabited α] [Add α] [One α] (x : α) : f x = f (f x) + 1 := sorry
opaque g [Inhabited α] : α → α → α
theorem geq [Inhabited α] (x : α) : g x x = x := sorry

/--
error: `grind` failed
case grind
α : Type u_1
inst : Inhabited α
inst_1 : Add α
inst_2 : One α
x z y : α
h : g y z = z
h_1 : g z y = g y x
h_2 : ¬f x = g x x
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] g y z = z
    [prop] g z y = g y x
    [prop] ¬f x = g x x
    [prop] f x = f (f x) + 1
    [prop] g x x = x
    [prop] f (f x) = f (f (f x)) + 1
    [prop] f (f (f x)) = f (f (f (f x))) + 1
  [eqc] False propositions
    [prop] f x = g x x
  [eqc] Equivalence classes
    [eqc] {x, g x x}
    [eqc] {z, g y z}
    [eqc] {f x, f (f x) + 1}
    [eqc] {g z y, g y x}
    [eqc] {f (f x), f (f (f x)) + 1}
    [eqc] {f (f (f x)), f (f (f (f x))) + 1}
  [ematch] E-matching patterns
    [thm] feq: [@f #4 #3 #0]
    [thm] geq: [@g #2 #1 #0 #0]
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 3)`
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] feq ↦ 3
    [thm] geq ↦ 1
-/
#guard_msgs (error) in
example [Inhabited α] [Add α] [One α] (x z y : α) : g y z = z → g z y = g y x → f x = g x x := by
  grind (gen := 3) [= feq, = geq]

/--
error: `grind` failed
case grind
x z y : Int
h : g y z = z
h_1 : g z y = g y x
h_2 : ¬f (f x) = g x x
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] g y z = z
    [prop] g z y = g y x
    [prop] ¬f (f x) = g x x
    [prop] f x + -1 * f (f x) + -1 = 0
    [prop] f (f x) + -1 * f (f (f x)) + -1 = 0
    [prop] g x x = x
    [prop] f (f (f x)) + -1 * f (f (f (f x))) + -1 = 0
  [eqc] False propositions
    [prop] f (f x) = g x x
  [eqc] Equivalence classes
    [eqc] {x, g x x}
    [eqc] {z, g y z}
    [eqc] {0, f x + -1 * f (f x) + -1, f (f x) + -1 * f (f (f x)) + -1, f (f (f x)) + -1 * f (f (f (f x))) + -1}
    [eqc] {g z y, g y x}
    [eqc] {f x + -1 * f (f x), f (f x) + -1 * f (f (f x)), f (f (f x)) + -1 * f (f (f (f x)))}
  [ematch] E-matching patterns
    [thm] feq: [@f #4 #3 #0]
    [thm] geq: [@g #2 #1 #0 #0]
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 2
    [assign] z := 3
    [assign] y := 4
    [assign] f x := 1
    [assign] f (f x) := 0
    [assign] g x x := 2
    [assign] g z y := 5
    [assign] g y x := 5
    [assign] g y z := 3
    [assign] f (f (f x)) := -1
    [assign] f (f (f (f x))) := -2
  [assoc] Operator `HAdd.hAdd`
    [basis] Basis
      [_] f (f (f x)) + -1 * f (f (f (f x))) = f x + -1 * f (f x)
      [_] f (f x) + -1 * f (f (f x)) = f x + -1 * f (f x)
      [_] f x + (-1 * f (f x) + -1) = 0
    [properties] Properties
      [_] commutative
      [_] identity: `0`
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 2)`
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] feq ↦ 3
    [thm] geq ↦ 1
-/
#guard_msgs (error) in
example (x z y : Int) : g y z = z → g z y = g y x → f (f x) = g x x := by
  grind (gen := 2) -ring [= feq, = geq]

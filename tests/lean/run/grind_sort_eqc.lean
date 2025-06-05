set_option grind.warning false
opaque f [Inhabited α] : α → α
@[grind =] theorem feq [Inhabited α] [Add α] [One α] (x : α) : f x = f (f x) + 1 := sorry
opaque g [Inhabited α] : α → α → α
@[grind =] theorem geq [Inhabited α] (x : α) : g x x = x := sorry

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
    [prop] g x x = x
    [prop] f x = f (f x) + 1
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
    [thm] geq: [@g #2 #1 #0 #0]
    [thm] feq: [@f #4 #3 #0]
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 3)`
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] feq ↦ 3
    [thm] geq ↦ 1
-/
#guard_msgs (error) in
example [Inhabited α] [Add α] [One α] (x z y : α) : g y z = z → g z y = g y x → f x = g x x := by
  grind (gen := 3)

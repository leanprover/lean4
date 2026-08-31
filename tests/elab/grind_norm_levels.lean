module
def g {α : Sort u} (a : α) := a

/--
error: `grind` failed
case grind
β : Type v
α : Type u
a c : α
b d : β
h : g (a, b) = (c, d)
h_1 : g (g (a, b)) = (c, d)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] g (a, b) = (c, d)
    [prop] g (g (a, b)) = (c, d)
  [eqc] Equivalence classes
    [eqc] {c, (g (g (a, b))).fst, (g (a, b)).fst}
      [eqc] {(c, d).fst}
    [eqc] {d, (g (g (a, b))).snd, (g (a, b)).snd}
      [eqc] {(c, d).snd}
    [eqc] {g (g (a, b)), g (a, b), (c, d), ((g (g (a, b))).fst, (g (g (a, b))).snd), ((g (a, b)).fst, (g (a, b)).snd)}
-/
#guard_msgs in
example {β : Type v} {α : Type u} (a c : α) (b d : β) : g.{max u v + 1} (a, b) = (c, d) → g (g.{max (u+1) (v+1)} (a, b)) = (c, d) → False := by
  grind

/--
error: `grind` failed
case grind
α : Type u
op : α → α → α
inst : Std.Associative op
a b c d : α
h : d = op b c
h_1 : ¬op a d = op (op a b) c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] Std.Associative op
    [prop] d = op b c
    [prop] ¬op a d = op (op a b) c
  [eqc] True propositions
    [prop] Std.Associative op
  [eqc] False propositions
    [prop] op a d = op (op a b) c
  [eqc] Equivalence classes
    [eqc] {d, op b c}
  [assoc] Operator `op`
    [diseqs] Disequalities
      [_] op a d ≠ op a (op b c)
-/
#guard_msgs in
example {α : Type u} (op : α → α → α) [Std.Associative op] (a b c d : α)
    : d = op b c → op a d = op (op a b) c := by
  grind => skip

example {α : Type u} (op : α → α → α) [Std.Associative op] (a b c d : α)
    : d = op b c → op a d = op (op a b) c := by
  grind => finish

example (x y : Nat) : x ≥ y + 1 → x > 0 := by
  grind => lia

example (x y : Nat) : x ≥ y + 1 → x > 0 := by
  grind => skip; lia; done

open Lean Grind

example [CommRing α] (a b c : α)
  : a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 + c^4 = 9 := by
  grind => ring

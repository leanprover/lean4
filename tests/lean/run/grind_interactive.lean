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

/--
trace: [facts] Asserted facts
  [_] (bs.set i₂ v₂ ⋯).size = bs.size
  [_] (as.set i₁ v₁ ⋯).size = as.size
  [_] (bs.set i₂ v₂ ⋯)[j] = if i₂ = j then v₂ else bs[j]
---
trace: [props] True propositions
  [_] j < (bs.set i₂ v₂ ⋯).size
  [_] j < bs.size
---
trace: [eqc] Equivalence classes
  [eqc] {bs, as.set i₁ v₁ ⋯}
  [eqc] {as.size, bs.size, (as.set i₁ v₁ ⋯).size, (bs.set i₂ v₂ ⋯).size}
  [eqc] {bs[j], (bs.set i₂ v₂ ⋯)[j]}
    [eqc] {if i₂ = j then v₂ else bs[j]}
  [eqc] others
    [eqc] {bs.set i₂ v₂ ⋯}
    [eqc] {↑as.size, ↑bs.size, ↑(bs.set i₂ v₂ ⋯).size}
-/
#guard_msgs in
example (as bs cs : Array α) (v₁ v₂ : α)
        (i₁ i₂ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : bs = as.set i₁ v₁)
        (h₃ : i₂ < bs.size)
        (h₃ : cs = bs.set i₂ v₂)
        (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind =>
    instantiate
    -- Display asserted facts with `generation > 0`
    show_asserted gen > 0
    -- Display propositions known to be `True`, containing `j`, and `generation > 0`
    show_true j && gen > 0
    -- Display equivalence classes with terms that contain `as` or `bs`
    show_eqcs as || bs
    instantiate

example {a b c d e : Nat}
    : a > 0 → b > 0 → c + e <= 1 → e = d → a*b + 2 > 2*c + 2*d := by
  grind =>
    have : a*b > 0 := Nat.mul_pos h h_1
    lia

example (as bs cs : Array α) (v₁ v₂ : α)
        (i₁ i₂ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : bs = as.set i₁ v₁)
        (h₃ : i₂ < bs.size)
        (h₃ : cs = bs.set i₂ v₂)
        (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
        (h₅ : j < cs.size)
        (h₆ : j < as.size)
        : cs[j] = as[j] := by
  grind =>
    have := fun h₁ h₂ => @Array.getElem_set _ bs i₂ h₁ v₂ j h₂
    instantiate

/--
error: `finish` failed
case grind
a b : Int
h : -1 * a + 1 ≤ 0
h_1 : -1 * b + 1 ≤ 0
h_2 : a * b ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] -1 * a + 1 ≤ 0
    [prop] -1 * b + 1 ≤ 0
    [prop] a * b ≤ 0
  [eqc] True propositions
    [prop] -1 * a + 1 ≤ 0
    [prop] -1 * b + 1 ≤ 0
    [prop] a * b ≤ 0
  [cutsat] Assignment satisfying linear constraints
    [assign] a := 1
    [assign] b := 1
-/
#guard_msgs in
example {a b : Int} : a > 0 → b > 0 → a*b > 0 := by
  grind => finish

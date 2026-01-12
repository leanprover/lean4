set_option warn.sorry false

/--
error: `grind` failed
case grind
α : Type u
op : α → α → α
inst✝ : Std.Associative op
a b c d : α
h✝¹ : d = op b c
h✝ : ¬op a d = op (op a b) c
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
  [eqc] {cs, bs.set i₂ v₂ ⋯}
  [eqc] {as.size, bs.size, cs.size, (as.set i₁ v₁ ⋯).size, (bs.set i₂ v₂ ⋯).size}
  [eqc] {cs[j], bs[j], (bs.set i₂ v₂ ⋯)[j]}
    [eqc] {if i₂ = j then v₂ else bs[j]}
  [eqc] {as.size = 0, bs.size = 0, cs.size = 0}
  [eqc] others
    [eqc] {↑as.size, ↑bs.size, ↑cs.size, ↑(bs.set i₂ v₂ ⋯).size}
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
    rename_i h1 h2 _ _ _
    have : a*b > 0 := Nat.mul_pos h1 h2
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
h✝² : -1 * a + 1 ≤ 0
h✝¹ : -1 * b + 1 ≤ 0
h✝ : a * b ≤ 0
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


/--
trace: [grind] Grind state
  [facts] Asserted facts
    [_] (bs.set i₂ v₂ ⋯).size = bs.size
    [_] (as.set i₁ v₁ ⋯).size = as.size
    [_] (bs.set i₂ v₂ ⋯)[j] = if i₂ = j then v₂ else bs[j]
  [props] True propositions
    [_] j < (bs.set i₂ v₂ ⋯).size
    [_] j < bs.size
  [eqc] Equivalence classes
    [eqc] {as.size, bs.size, cs.size, (as.set i₁ v₁ ⋯).size, (bs.set i₂ v₂ ⋯).size}
    [eqc] {cs[j], bs[j], (bs.set i₂ v₂ ⋯)[j]}
      [eqc] {if i₂ = j then v₂ else bs[j]}
    [eqc] {as.size = 0, bs.size = 0, cs.size = 0}
    [eqc] others
      [eqc] {↑as.size, ↑bs.size, ↑cs.size, ↑(bs.set i₂ v₂ ⋯).size}
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
    show_state gen > 0
    instantiate

/--
trace: [splits] Case split candidates
  [split] #7a08 := ¬p ∨ ¬q
  [split] #8212 := ¬p ∨ q
  [split] #fc16 := p ∨ ¬q
  [split] #4283 := p ∨ q
  [split] #0457 := p ∨ r
-/
#guard_msgs (trace) in
example (r p q : Prop) : p ∨ r → p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind =>
    show_cases
    sorry

/--
trace: [splits] Case split candidates
  [split] #65fc := p ∨ p₁ = p₂
  [split] #1460 := p ∨ q ∧ r
-/
example (r p q p₁ p₂ : Prop) : (p₁ → q) → p ∨ (q ∧ r) → p ∨ (p₁ ↔ p₂) → False := by
  grind =>
    show_cases
    sorry

def h (as : List Nat) :=
  match as with
  | []      => 1
  | [_]     => 2
  | _::_::_ => 3

/--
trace: [splits] Case split candidates
  [split] #829a := match bs with
      | [] => 1
      | [head] => 2
      | head :: head_1 :: tail => 3
  [split] #dce6 := match as with
      | [] => 1
      | [head] => 2
      | head :: head_1 :: tail => 3
-/
#guard_msgs (trace) in
example : h bs = 1 → h as ≠ 0 := by
  grind [h.eq_def] =>
    instantiate
    show_cases
    sorry

example : h bs = 1 → h as ≠ 0 := by
  grind [h.eq_def] =>
    instantiate
    show_cases
    cases #dce6
    instantiate
    focus instantiate
    instantiate

/--
error: Failed here
case grind
bs as : List Nat
h✝¹ : h bs = 1
h✝ : h as = 0
⊢ False
-/
#guard_msgs in
example : h bs = 1 → h as ≠ 0 := by
  grind [h.eq_def] =>
    skip
    try fail
    fail_if_success fail
    first (fail) (done) (skip)
    fail "Failed here"
    done

example : h bs = 1 → h as ≠ 0 := by
  grind [h.eq_def] =>
    instantiate | as
    cases #dce6
    all_goals instantiate

/--
info: Try these:
  [apply] cases #7a08 for
    ¬p ∨ ¬q
  [apply] cases #8212 for
    ¬p ∨ q
  [apply] cases #fc16 for
    p ∨ ¬q
  [apply] cases #4283 for
    p ∨ q
  [apply] cases #0457 for
    p ∨ r
-/
#guard_msgs in
example (r p q : Prop) : p ∨ r → p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind =>
    cases?
    sorry

set_option trace.Meta.debug true in
example (r p q : Prop) : p ∨ r → p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind =>
    cases?
    sorry

/--
info: Try these:
  [apply] cases #7a08 for
    ¬p ∨ ¬q
  [apply] cases #8212 for
    ¬p ∨ q
  [apply] cases #fc16 for
    p ∨ ¬q
-/
#guard_msgs in
example (r p q : Prop) : p ∨ r → p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind =>
    cases? p && Not
    sorry

example : h bs = 1 → h as ≠ 0 := by
  grind [h.eq_def] =>
    instantiate
    cases #dce6 <;> instantiate

example : h bs = 1 → h as ≠ 1 := by
  grind [h.eq_def] =>
    instantiate
    cases #dce6
    any_goals instantiate
    sorry

/--
error: unsolved goals
bs as : List Nat
h✝² : h bs = 1
h✝¹ : h as = 0
h✝ : as = []
⊢ False
-/
#guard_msgs in
example : h bs = 1 → h as ≠ 0 := by
  grind -verbose [h.eq_def] =>
    instantiate
    cases #dce6
    next => skip
    all_goals sorry

def g (as : List Nat) :=
  match as with
  | []      => 1
  | [_]     => 2
  | _::_::_ => 3

example : g bs = 1 → g as ≠ 0 := by
  grind [g.eq_def] =>
    instantiate
    cases #dce6
    next => instantiate
    next => finish
    tactic =>
      rename_i h_1 _ _ _ h_2
      rw [h_2] at h_1
      simp [g] at h_1

open Std
example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] (a b c : α)
    : (2:Int) • a + b < c + a + a → b = c → False := by
  grind => linarith

example {α : Sort u} (op : α → α → α) [Associative op] (a b c : α)
    : op a (op b b) = c → op c c = op (op c a) (op b b) := by
  grind => ac

/--
error: The tactic provided to `fail_if_success` succeeded but was expected to fail:
  ac
-/
#guard_msgs in
example {α : Sort u} (op : α → α → α) [Associative op] (a b c : α)
    : op a (op b b) = c → op c c = op (op c a) (op b b) := by
  grind => fail_if_success ac

example {α : Sort u} (op : α → α → α) [Associative op] (a b c : α)
    : op a (op b b) = c → op c c = op (op c a) (op b b) := by
  grind =>
    fail_if_success linarith
    ac

/--
trace: [cutsat] Assignment satisfying linear constraints
  [assign] y := 3
  [assign] z := 0
  [assign] x := 4
-/
#guard_msgs in
example : y > (z+1)*2 → x > y → x > 10 := by
  grind =>
    lia
    sorry

/--
trace: [ring] Ring `Int`
  [basis] Basis
    [_] 2 * (z * x) + 2 * x + -1 = 0
    [_] y + -2 * z + -2 = 0
  [diseqs] Disequalities
    [_] ¬x = 0
-/
#guard_msgs in
example {y z x : Int} : y = (z+1)*2 → x*y = 1 → x = 0 := by
  grind =>
    ring
    sorry

#guard_msgs in
example {y z x : Int} : y = (z+1)*2 → x*y = 1 → x = 0 := by
  grind -verbose =>
    ring
    sorry

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
    instantiate only [Array.getElem_set] | gen > 0
    instantiate only [Array.getElem_set]

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
    instantiate only [= Array.getElem_set]
    instantiate only [← Array.getElem_set]

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
    repeat instantiate only [= Array.getElem_set]

/--
trace: [grind.ematch.instance] Array.getElem_set: (as.set i₁ v₁ ⋯)[j] = if i₁ = j then v₁ else as[j]
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
    set_option trace.grind.ematch.instance true in
    instantiate

opaque p : Nat → Prop
opaque q : Nat → Prop
opaque f : Nat → Nat
opaque finv : Nat → Nat

axiom pq : p x → q x
axiom fInj : finv (f x) = x

example : f x = f y → p x → q y := by
  grind =>
    instantiate only [→pq, !fInj]

/--
trace: [thms] Local theorems
  [thm] #c5bb := ∀ (x : Nat), q x
  [thm] #bfb8 := ∀ (x : Nat), p x → p (f x)
-/
#guard_msgs in
example : (∀ x, q x) → (∀ x, p x → p (f x)) → p x → p (f (f x)) := by
  grind =>
    show_local_thms
    instantiate only [#bfb8]

example : (∀ x, q x) → (∀ x, p x → p (f x)) → p x → p (f (f x)) := by
  grind =>
    show_local_thms
    instantiate only [#bfb8]

/-- error: no local theorems -/
#guard_msgs in
example : (∀ x, q x) → (∀ x, p x → p (f x)) → p x → p (f (f x)) := by
  grind =>
    instantiate only [#abcd]

/--
error: unsolved goals
case grind
r p q : Prop
h✝² : p ∨ r
h1 : p ∨ q
h✝¹ : p ∨ ¬q
h2 : ¬p ∨ q
h✝ : ¬p ∨ ¬q
⊢ False
-/
#guard_msgs in
example (r p q : Prop) : p ∨ r → p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind -verbose =>
    rename_i h1 _ h2 _
    done

namespace Ex1
@[grind cases]
structure Point (α : Type) where
  x : α
  y : α

opaque p : Point Nat → Prop

@[grind =] theorem pax : p { x, y } ↔ (x < y ∨ x > y) := by sorry

example : (a : Point Nat) → p a → x ≠ y → False := by
  intro a
  grind =>
    cases #6ccb
    instantiate only [pax]
    show_cases
    rename_i y w _ -- Must reset cached anchors
    show_cases
    cases #e2a6
    all_goals sorry

example : (a : Point Nat) → p a → x ≠ y → False := by
  intro a
  grind =>
    cases #6ccb
    instantiate only [pax]
    show_cases
    next y w _ =>
    show_cases
    cases #e2a6
    all_goals sorry

example : (a : Point Nat) → p a → x ≠ y → False := by
  grind =>
    expose_names
    cases #6ccb
    sorry

opaque q : Nat → Nat → Prop
axiom qax : x ≠ y → q x y

example : x > y + 1 → q x y := by
  grind =>
    have h : x > y
    have : x ≠ y
    have : x > y := h
    instantiate [qax]

/--
error: `finish` failed
x y : Nat
h✝² : y + 2 ≤ x
h✝¹ : ¬q x y
h✝ : x ≤ y + 2
⊢ False
-/
#guard_msgs in
example : x > y + 1 → q x y := by
  grind -verbose =>
    have h : x > y + 2

end Ex1

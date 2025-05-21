abbrev f (a : α) := a
set_option grind.warning false
set_option grind.debug true
set_option grind.debug.proofs true

/--
error: `grind` failed
case grind
a b c : Bool
p q : Prop
left : a = true
right : b = true ∨ c = true
left_1 : p
right_1 : q
h_1 : b = false ∨ a = false
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a = true
    [prop] b = true ∨ c = true
    [prop] p
    [prop] q
    [prop] b = false ∨ a = false
  [eqc] True propositions
    [prop] b = true ∨ c = true
    [prop] p
    [prop] q
    [prop] b = false ∨ a = false
    [prop] b = false
    [prop] c = true
  [eqc] False propositions
    [prop] a = false
    [prop] b = true
  [eqc] Equivalence classes
    [eqc] {b, false}
    [eqc] {a, c, true}
-/
#guard_msgs (error) in
theorem ex (h : (f a && (b || f (f c))) = true) (h' : p ∧ q) : b && a := by
  grind

section
attribute [local grind cases eager] Or

/--
error: `grind` failed
case grind.2.1
a b c : Bool
p q : Prop
left : a = true
h_1 : c = true
left_1 : p
right_1 : q
h_3 : b = false
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a = true
    [prop] c = true
    [prop] p
    [prop] q
    [prop] b = false
  [eqc] True propositions
    [prop] p
    [prop] q
  [eqc] Equivalence classes
    [eqc] {b, false}
    [eqc] {a, c, true}
[grind] Diagnostics
  [cases] Cases instances
    [cases] Or ↦ 3
-/
#guard_msgs (error) in
theorem ex2 (h : (f a && (b || f (f c))) = true) (h' : p ∧ q) : b && a := by
  grind

end

def g (i : Nat) (j : Nat) (_ : i > j := by omega) := i + j

/--
trace: [grind.offset.model] i := 1
[grind.offset.model] j := 0
[grind.offset.model] 「0」 := 0
[grind.offset.model] 「i + j」 := 0
[grind.offset.model] 「i + 1」 := 2
[grind.offset.model] 「i + j + 1」 := 1
-/
#guard_msgs (trace) in
set_option trace.grind.offset.model true in
example (i j : Nat) (h : i + 1 > j + 1) : g (i+1) j = f ((fun x => x) i) + f j + 1 := by
  fail_if_success grind
  sorry

structure Point where
  x : Nat
  y : Int

/--
error: `grind` failed
case grind
a₁ : Point
a₂ : Nat
a₃ : Int
as : List Point
b₁ : Point
bs : List Point
b₂ : Nat
b₃ : Int
head_eq : a₁ = b₁
x_eq : a₂ = b₂
y_eq : a₃ = b₃
tail_eq_1 : as = bs
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a₁ = b₁
    [prop] a₂ = b₂
    [prop] a₃ = b₃
    [prop] as = bs
  [eqc] Equivalence classes
    [eqc] {as, bs}
    [eqc] {a₃, b₃}
    [eqc] {a₂, b₂}
    [eqc] {a₁, b₁}
-/
#guard_msgs (error) in
theorem ex3 (h : a₁ :: { x := a₂, y := a₃ : Point } :: as = b₁ :: { x := b₂, y := b₃} :: bs) : False := by
  grind

def h (a : α) := a

example (p : Prop) (a b c : Nat) : p → a = 0 → a = b → h a = h c → a = c ∧ c = a → a = b ∧ b = a → a = c := by
  grind

set_option trace.grind.debug.proof true
/--
error: `grind` failed
case grind.1
α : Type
a : α
p q r : Prop
h₁ : HEq p a
h₂ : HEq q a
h₃ : p = r
left : p
right : r
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] HEq p a
    [prop] HEq q a
    [prop] p = r
    [prop] p
    [prop] r
  [eqc] True propositions
    [prop] p = r
    [prop] a
    [prop] p
    [prop] q
    [prop] r
  [cases] Case analyses
    [cases] [1/2]: p = r
-/
#guard_msgs (error) in
example (a : α) (p q r : Prop) : (h₁ : HEq p a) → (h₂ : HEq q a) → (h₃ : p = r) → False := by
  grind

example (a b : Nat) (f : Nat → Nat) : (h₁ : a = b) → (h₂ : f a ≠ f b) → False := by
  grind

example (a : α) (p q r : Prop) : (h₁ : HEq p a) → (h₂ : HEq q a) → (h₃ : p = r) → q = r := by
  grind

/--
trace: [grind.issues] found congruence between
      g b
    and
      f a
    but functions have different types
-/
#guard_msgs (trace) in
set_option trace.grind.issues true in
set_option trace.grind.debug.proof false in
example (f : Nat → Bool) (g : Int → Bool) (a : Nat) (b : Int) : HEq f g → HEq a b → f a = g b := by
  fail_if_success grind
  sorry

/--
error: `grind` failed
case grind
f : Nat → Bool
g : Int → Bool
a : Nat
b : Int
h : HEq f g
h_1 : HEq a b
h_2 : ¬f a = g b
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] HEq f g
    [prop] HEq a b
    [prop] ¬f a = g b
  [eqc] False propositions
    [prop] f a = g b
  [eqc] Equivalence classes
    [eqc] {a, b}
    [eqc] {f, g}
[grind] Issues
  [issue] found congruence between g b and f a but functions have different types
-/
#guard_msgs (error) in
example (f : Nat → Bool) (g : Int → Bool) (a : Nat) (b : Int) : HEq f g → HEq a b → f a = g b := by
  grind

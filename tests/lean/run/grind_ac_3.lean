set_option warn.sorry false
set_option grind.debug true

opaque op : Int → Int → Int
instance : Std.Associative op := sorry
instance : Std.Commutative op := sorry
local infixr:64 "∘" => op

variable (a b c d e f g h i j k l x y z p q r s t u v w : Int)

open Lean Grind AC

example (a b c d : Int)
    : a∘b = b∘c → c∘c = d∘c →
      d∘a∘b∘d = a∘a∘b∘d := by
  grind only

example : a ∘ a ∘ b ∘ c ∘ b ∘ d = d ∘ b ∘ a ∘ c ∘ a ∘ b := by
  grind only

example : ((a ∘ (b ∘ c)) ∘ (d ∘ e)) ∘ f = f ∘ (e ∘ (d ∘ (c ∘ (b ∘ a)))) := by
  grind only

example (h₁ : a = b) : a ∘ c = c ∘ b := by
  grind only

example (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) :
    (a ∘ x) ∘ y = y ∘ (x ∘ d) := by
  grind only

example (h₁ : a = b) (h₂ : c = d) :
    a ∘ c ∘ e = e ∘ (b ∘ d) := by
  grind only

example (h₁ : a ∘ b = c ∘ d) :
    a ∘ b ∘ e = e ∘ c ∘ d := by
  grind only

example (h₁ : a ∘ b = c ∘ d) :
    d ∘ c ∘ e ∘ f = f ∘ e ∘ b ∘ a := by
  grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : d ∘ e = f ∘ g) :
    a ∘ b ∘ e = c ∘ f ∘ g := by
  grind only

example (h₁ : a ∘ a = b ∘ b) :
    a ∘ a ∘ a ∘ a = b ∘ b ∘ b ∘ b := by
  grind only

example :
    a ∘ a ∘ b ∘ c ∘ c ∘ c ∘ d = c ∘ a ∘ d ∘ a ∘ c ∘ b ∘ c := by
  grind only

example :
    ((a ∘ b) ∘ (c ∘ (d ∘ e))) ∘ (f ∘ g)
  = g ∘ f ∘ e ∘ d ∘ c ∘ b ∘ a := by
  grind only

example (h₁ : a ∘ d = e ∘ f) :
    ((a ∘ b) ∘ (c ∘ d)) ∘ g = g ∘ ((e ∘ f) ∘ (b ∘ c)) := by
  grind only

example (h₁ : a = c) (h₂ : b = d) :
    (a ∘ b ∘ a ∘ b) = (c ∘ d ∘ c ∘ d) := by
  grind only

example (h₁ : a = c) (h₂ : b = d) :
    (a ∘ b ∘ a ∘ b) = (c ∘ d ∘ c ∘ d) := by
  grind only

example (h₁ : a ∘ b = c ∘ d) :
    z ∘ y ∘ a ∘ w ∘ b = w ∘ z ∘ y ∘ d ∘ c := by
  grind only

example (h₁ : a ∘ b = c ∘ d) :
    z ∘ y ∘ a ∘ w ∘ b = w ∘ z ∘ y ∘ d ∘ c := by
  grind only

example (h₁ : a = d) (h₂ : c = b) :
    (a ∘ b ∘ c ∘ e) = (d ∘ b ∘ b ∘ e) := by
  grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : e ∘ f = g ∘ h) :
    (a ∘ e) ∘ (b ∘ f) ∘ i = (d ∘ h) ∘ (c ∘ g) ∘ i := by
  grind only

example (h₁ : a = b) :
    (a ∘ c) ∘ (d ∘ a) = (b ∘ d) ∘ (c ∘ b) := by
  grind only

example (h₁ : a = e) (h₂ : b = f) (h₃ : c = g) (h₄ : d = h) :
    (a ∘ b ∘ c ∘ d) = (h ∘ g ∘ f ∘ e) := by
  grind only

example :
    (((a ∘ b) ∘ c) ∘ ((d ∘ e) ∘ (f ∘ g))) ∘ ((h ∘ i) ∘ j)
  = j ∘ i ∘ h ∘ g ∘ f ∘ e ∘ d ∘ c ∘ b ∘ a := by
  grind only

example (h₁ : a ∘ b = c ∘ d) :
    (a ∘ x ∘ b) ∘ (y ∘ a ∘ b) = (x ∘ y) ∘ (c ∘ c ∘ d ∘ d) := by
  grind only

example (h₁ : a ∘ a = b ∘ c) (h₂ : c ∘ d = e ∘ f) :
    a ∘ a ∘ d = b ∘ e ∘ f := by
  grind only

example (a b c d e f g : Int)
    (h₁ : a ∘ b = c ∘ d) (h₂ : b ∘ e = f ∘ g) :
    a ∘ e ∘ b ∘ b = d ∘ c ∘ f ∘ g := by
  grind only

example (a b c d e f g : Int)
    (h₁ : a ∘ b = c ∘ d) (h₃ : e = f ∘ g) :
    a ∘ e ∘ b = d ∘ c ∘ f ∘ g := by
  grind only

example (h₁ : p ∘ q = r ∘ s) (h₂ : r ∘ t = v ∘ w) :
    q ∘ t ∘ p = w ∘ v ∘ s := by
  grind only

example (h₁ : p ∘ q = r ∘ s) (h₂ : r ∘ t = v ∘ w) :
    q ∘ t ∘ p ∘ r = s ∘ v ∘ w ∘ r := by
  grind only

example
    (h₁ : p ∘ q = r ∘ s)
    (h₂ : q ∘ t = s ∘ u)
    (h₃ : t ∘ v = u ∘ w) :
    p ∘ q ∘ t ∘ v ∘ q ∘ t = r ∘ s ∘ s ∘ u ∘ u ∘ w := by
  grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : b ∘ e = d ∘ f) (h₄ : b ∘ g = d ∘ h) :
    a ∘ e ∘ g ∘ b ∘ b ∘ b = c ∘ d ∘ d ∘ f ∘ d ∘ h := by
  grind only

example (h₁ : u ∘ v = w ∘ x) (h₂ : v ∘ y = x ∘ z) :
    k ∘ u ∘ y ∘ v ∘ v ∘ j = j ∘ k ∘ w ∘ x ∘ x ∘ z := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₂ : b ∘ e = d ∘ f)
    (h₃ : e ∘ g = f ∘ h)
    (h₄ : g ∘ i = h ∘ j)
    (h₅ : i ∘ k = j ∘ l) :
    a ∘ b ∘ e ∘ g ∘ i ∘ k ∘ b ∘ e ∘ g ∘ i
      = c ∘ d ∘ d ∘ f ∘ f ∘ h ∘ h ∘ j ∘ j ∘ l := by
  grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : e ∘ c = f ∘ b) :
    e ∘ a ∘ b ∘ c = f ∘ d ∘ c ∘ b := by
  grind only

example (h₁ : p ∘ q = r ∘ s) (h₂ : q ∘ t = s ∘ u) :
    p ∘ t ∘ q ∘ q = r ∘ s ∘ s ∘ u := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₂ : b ∘ e = d ∘ f)
    (h₃ : e ∘ g = f ∘ h)
    (h₄ : g ∘ i = h ∘ j)
    (h₅ : i ∘ k = j ∘ l) :
    a ∘ k ∘ b ∘ b ∘ e ∘ e ∘ g ∘ g ∘ i ∘ i
      = c ∘ l ∘ d ∘ d ∘ f ∘ f ∘ h ∘ h ∘ j ∘ j := by
  grind only

example (h₁ : p ∘ q = r ∘ s) (h₂ : q ∘ t = s ∘ u) (h₃ : t ∘ v = u ∘ w) :
    p ∘ v ∘ q ∘ q ∘ t ∘ t = r ∘ w ∘ s ∘ s ∘ u ∘ u := by
 grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : b ∘ e = d ∘ f) :
    a ∘ e ∘ b ∘ b = c ∘ d ∘ d ∘ f := by
  grind only

example (u v w x y z k j : Int)
    (h₁ : u ∘ v = w ∘ x) (h₂ : v ∘ y = x ∘ z) :
    k ∘ u ∘ y ∘ v ∘ v ∘ j = j ∘ k ∘ w ∘ x ∘ x ∘ z := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₂ : b ∘ e = d ∘ f)
    (h₃ : e ∘ g = f ∘ h)
    (h₄ : g ∘ i = h ∘ j)
    (h₅ : i ∘ k = j ∘ l) :
    a ∘ k ∘ b ∘ b ∘ e ∘ e ∘ e ∘ g ∘ g ∘ i ∘ j
      = c ∘ l ∘ d ∘ f ∘ d ∘ f ∘ f ∘ h ∘ h ∘ j ∘ j := by
  grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : b ∘ e = d ∘ f) :
    c ∘ d ∘ e = a ∘ d ∘ f := by
  grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : b ∘ e = d ∘ f) (h₃ : b ∘ g = d ∘ h) :
    c ∘ d ∘ f ∘ g = c ∘ d ∘ h ∘ e := by
  grind only

example (h1 : a ∘ b = c ∘ d) (h2 : b ∘ e = d ∘ f) :
    c ∘ d ∘ e = a ∘ d ∘ f := by
 grind only

 example (h1 : p ∘ q = r ∘ s) (h2 : q ∘ t = s ∘ u) :
    r ∘ s ∘ t = p ∘ s ∘ u := by
  grind only

example (h1 : a ∘ b = c ∘ d) (h2 : b ∘ e = d ∘ f) (h3 : b ∘ g = d ∘ h) :
    c ∘ d ∘ f ∘ g = c ∘ d ∘ h ∘ e := by
  grind only

example (h1 : a ∘ b = c ∘ d) (h2 : b ∘ e = d ∘ f) (h3 : e ∘ g = f ∘ h) :
    c ∘ d ∘ h ∘ f = a ∘ d ∘ g ∘ f := by
  grind only

example (h1 : a ∘ b = c ∘ d) (h2 : b ∘ e = d ∘ f) :
    c ∘ d ∘ e = a ∘ d ∘ f := by
  grind only

example (a b c d e f : Int) (h1 : max a b = max c d) (h2 : max b e = max d f) :
    max c (max d e) = max (max a d) f := by
  grind -lia only

example (a b c d e f g h : Nat) :
    max a b = max c d → max b e = max d f → max b g = max d h →
    max (max c d) (max f g) = max (max c d) (max h e) := by
  grind -lia only

example (a b c d e f g h : Nat) :
    max a b = max c d → max b e = max (max d 0) f → max b g = max d h →
    max (max c d) (max f g) = max (max c d) (max (max 0 h) e) := by
  grind -lia only

example (a b c d e f g h : Nat) :
    max a b = max c d → max b e = max d f → max b g = max d h →
    max (max f d) (max c g) = max (max e d) (max h c) := by
  grind -lia only

example (a b c d e f g h : Nat) :
    max a b = max c d → max b e = max d f → max b g = max d h →
    max (max f d) (max c g) = max (max e (max d (max b (max c e)))) h := by
  grind -lia only

example {α} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c d : α)
    : op a b = op b c → op c c = op d c →
      op (op d a) (op b d) = op (op a a) (op b d) := by
  grind only

example {α} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (u : α) [Std.LawfulIdentity op u]
    (a b c d e : α)
    : e = u →
      op (op a u) b = op (op b e) c → op c c = op d (op u c) →
      op (op d a) (op b (op d e)) = op (op a a) (op (op u b) d) := by
  grind only

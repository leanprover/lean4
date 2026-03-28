set_option grind.debug true
set_option warn.sorry false
opaque op : Int → Int → Int
instance : Std.Associative op := sorry
local infixr:64 " ∘ " => op

variable (a b c d e f g h i j k m n p q r s t u v w x y z : Int)

example : ((a ∘ b) ∘ c) ∘ d = a ∘ (b ∘ (c ∘ d)) := by
  grind only

example : (a ∘ (b ∘ c)) ∘ (d ∘ e) = a ∘ (b ∘ (c ∘ (d ∘ e))) := by
  grind only

example (h₁ : a ∘ b = c ∘ d) : (x ∘ a) ∘ b ∘ y = x ∘ c ∘ d ∘ y := by
  grind only

example (h₁ : a ∘ b = c ∘ d) (h₂ : b ∘ e = f ∘ g) :
    (c ∘ d) ∘ e = a ∘ (f ∘ g) := by
  grind only

example (h₁ : b ∘ c = d ∘ e) (h₂ : a ∘ b = f ∘ g) :
    a ∘ (d ∘ e) = (f ∘ g) ∘ c := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₂ : b ∘ e = f ∘ g)
    (h₃ : e ∘ h = i ∘ j) :
    (c ∘ d) ∘ i ∘ j = a ∘ (f ∘ g) ∘ h := by
  grind only

example
    (h₁ : b ∘ c = f ∘ g)
    (h₂ : e ∘ b = p ∘ q) :
    (p ∘ q) ∘ c = e ∘ (f ∘ g) := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₂ : e ∘ f = g ∘ h) :
    (c ∘ d) ∘ (e ∘ f) = a ∘ (b ∘ (g ∘ h)) := by
  grind only

example
    (h₁ : u ∘ v = w ∘ x)
    (h₂ : v ∘ y = r ∘ s) :
    z ∘ (w ∘ x) ∘ y ∘ t = z ∘ u ∘ (r ∘ s) ∘ t := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₃ : b ∘ g = m ∘ n) :
    (c ∘ d) ∘ g = a ∘ (m ∘ n) := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₂ : d ∘ e = i ∘ j) :
    (a ∘ b) ∘ e = c ∘ (i ∘ j) := by
  grind only

example
    (h₁ : a ∘ b = c ∘ d)
    (h₂ : b ∘ e = f ∘ g)
    (h₃ : g ∘ h = i ∘ j) :
    (c ∘ d) ∘ e ∘ h = a ∘ f ∘ (i ∘ j) := by
  grind only

example
   : b ∘ e = f →
     a ∘ c = x ∘ y →
     b ∘ d = y ∘ z →
     x ∘ b ∘ d = a ∘ c ∘ z := by
  grind only

example
   : x ∘ f = h →
     y ∘ g = i →
     a ∘ b = x ∘ x →
     b ∘ a = y ∘ y →
     x ∘ x ∘ a ∘ b ∘ x ∘ x = a ∘ y ∘ y ∘ y ∘ y ∘ b := by
  grind

example
   : a ∘ b = x →
     b ∘ a = y →
     x ∘ a ∘ b ∘ x = a ∘ y ∘ y ∘ b := by
  grind

example
   : a ∘ b = c →
     b ∘ a = d →
     c ∘ a ∘ b ∘ c = a ∘ d ∘ d ∘ b := by
  grind

example {α} (op : α → α → α) [Std.Associative op] (a b c d : α)
   : op a b = c →
     op b a = d →
     op (op c a) (op b c) = op (op a d) (op d b) := by
  grind

example {α} (op : α → α → α) [Std.Associative op] (u : α) [Std.LawfulIdentity op u] (a b c d : α)
   : op u (op a b) = op u c →
     op b (op a u) = op d u →
     op (op c a) (op (op b u) c) = op (op a d) (op d b) := by
  grind

example {α} (f : α → α) (op : α → α → α) [Std.Associative op] (u : α) [Std.LawfulIdentity op u] (a b c d : α)
   : op u (op a b) = op u c →
     op b (op a u) = op d u →
     f (f (op (op c a) (op (op b u) c))) = f (f (op (op a d) (op d b))) := by
  grind

example {α} (a b c d : List α)
   : a ++ b = c →
     b ++ a = d →
     c ++ a ++ b ++ c = a ++ d ++ d ++ b := by
  grind only

example {α} (a b c d : List α)
   : a ++ b = c ++ c  →
     b ++ a = d ++ d →
     c ++ c ++ a ++ b ++ c ++ c = a ++ d ++ d ++ d ++ d ++ b := by
  grind only

example {α} (a b c d : List α)
   : a ++ b = c ++ [] ++ c  →
     b ++ a = d ++ d →
     c ++ c ++ a ++ [] ++ b ++ c ++ c = a ++ d ++ [] ++ d ++ d ++ d ++ b := by
  grind only

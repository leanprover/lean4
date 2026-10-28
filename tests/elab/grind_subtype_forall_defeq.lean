/-!
`Subtype.forall` in the `grind` normalizer (#15748) turns `∀ x : {b // p b}, q (f x)` into
`∀ b (h : p b), q (f ⟨b, h⟩)`. The instance for `f ⟨b, hb⟩` then has the side condition `p b`,
which `grind` must prove. When the proof `hb` stored in `⟨b, hb⟩` has a type that is only
definitionally equal to `p b`, the side condition is not available and the instance is never used.
Found in cslib (`theoryEq_isBisimulation`).
-/

def img (R : α → α → Prop) (a : α) : α → Prop := fun b => R a b
def diag (R : α → α → Prop) (a b : α) : Prop := R a b
def mem (s : α → Prop) (a : α) : Prop := s a

/-! Side condition stated as `p b` syntactically. -/

example (p : α → Prop) (f : {b // p b} → β) (q : β → Prop)
    (h : ∀ x : {b // p b}, q (f x)) (hb : p b) : q (f ⟨b, hb⟩) := by
  grind

example (p : α → Prop) (f : {b // p b} → β) (q : β → Prop) (g : ∀ b, p b)
    (h : ∀ x : {b // p b}, q (f x)) : q (f ⟨b, g b⟩) := by
  grind

example (p : α → Prop) (f : {b // p b} → β) (q : β → Prop)
    (h : ∀ x : {b // p b}, q (f x)) (x : {b // p b}) : q (f x) := by
  grind

example (p : α → Prop) (f : {b // p b} → β) (g : α → {b // p b}) (q : β → Prop)
    (h : ∀ x : {b // p b}, q (f x)) (a : α) : q (f (g a)) := by
  grind

/-! Side condition up to beta or arithmetic. -/

example (R : α → α → Prop) (f : {b // (fun b => R a b) b} → β) (q : β → Prop)
    (h : ∀ x : {b // (fun b => R a b) b}, q (f x)) (hab : R a b) : q (f ⟨b, hab⟩) := by
  grind

example (f : {n : Nat // 0 < n} → β) (q : β → Prop)
    (h : ∀ x : {n : Nat // 0 < n}, q (f x)) (hn : 1 ≤ n) : q (f ⟨n, hn⟩) := by
  grind

example (f : {n : Nat // 0 < n} → β) (q : β → Prop)
    (h : ∀ x : {n : Nat // 0 < n}, q (f x)) (hn : n ≠ 0) : q (f ⟨n, Nat.pos_of_ne_zero hn⟩) := by
  grind

/-! Properties, equality, and existentials of subtypes. -/

example (p : α → Prop) (x : {b // p b}) : p x.val := by
  grind

example (p : α → Prop) (f : α → {b // p b}) (a : α) : p (f a).val := by
  grind

example (p : α → Prop) (f : α → {b // p b}) (q : α → Prop)
    (h : ∀ b, p b → q b) (a : α) : q (f a).val := by
  grind

example (p q : α → Prop) (x : {y : {b // p b} // q y.val}) : p x.val.val ∧ q x.val.val := by
  grind

example (p : α → Prop) (hb : p b) (q : α → Prop) (hq : q b) :
    q (Subtype.val (⟨b, hb⟩ : {b // p b})) := by
  grind

example (p : α → Prop) (h1 h2 : p a) : (⟨a, h1⟩ : {b // p b}) = ⟨a, h2⟩ := by
  grind

example (p : α → Prop) (x y : {b // p b}) (h : x.val = y.val) : x = y := by
  grind

example (p q : α → Prop) (ha : p a) (hq : q a) : ∃ x : {b // p b}, q x.val := by
  grind

example (p q : α → Prop) (h : ∀ x : {b // p b}, q x.val) (hc : p c) : q c := by
  grind

example (R : α → α → Prop) (q : α → Prop) (h : ∃ x : {b // img R a b}, q x.val) :
    ∃ b, img R a b ∧ q b := by
  grind

/-! Ground reasoning about subtypes: projections, injectivity, eta, congruence. -/

example (p : α → Prop) (hb : p b) : (⟨b, hb⟩ : {b // p b}).val = b := by
  grind

example (p : α → Prop) (x : {b // p b}) : x = ⟨x.val, x.property⟩ := by
  grind

example (p : α → Prop) (x : {b // p b}) : (⟨x.val, x.property⟩ : {b // p b}).val = x.val := by
  grind

example (p : α → Prop) (h1 : p a) (h2 : p b) (h : (⟨a, h1⟩ : {b // p b}) = ⟨b, h2⟩) : a = b := by
  grind

example (p : α → Prop) (x : {b // p b}) (hb : p b) (h : x.val = b) : x = ⟨b, hb⟩ := by
  grind

example (p : α → Prop) (x : {b // p b}) (h : x.val = c) : p c := by
  grind

example (p : α → Prop) (f : α → {b // p b}) (h : (f a).val = c) : p c := by
  grind

example (p : α → Prop) (f : {b // p b} → β) (h1 h2 : p a) : f ⟨a, h1⟩ = f ⟨a, h2⟩ := by
  grind

example (p : α → Prop) (f : {b // p b} → β) (h1 : p a) (h2 : p b) (h : a = b) :
    f ⟨a, h1⟩ = f ⟨b, h2⟩ := by
  grind

example (p : Nat → Prop) (x y : {n // p n}) (h : x.val = y.val) : (x == y) = true := by
  grind

example (p : α → Prop) (hb : p b) : ∃ x : {b // p b}, x.val = b := by
  grind

example (p : α → Prop) (hb : ¬ p b) : ∀ x : {b // p b}, x.val ≠ b := by
  grind

example (p : α → Prop) (x : {b // p b}) (h : ∀ y : {b // p b}, y.val = x.val) (y : {b // p b}) :
    y = x := by
  grind

example (p : α → Prop) (x : {f : α → α // ∀ a, p (f a)}) (a : α) : p (x.val a) := by
  grind

example (p : α → Prop) (x : {b // p b}) : (match x with | ⟨v, _⟩ => v) = x.val := by
  grind

example (p : α → Prop) [DecidablePred p] (x : {b // p b}) : (if p x.val then 1 else 0) = 1 := by
  grind

/-! Side condition only definitionally equal to the stored proof's type. -/

example (R : α → α → Prop) (f : {b // img R a b} → β) (q : β → Prop)
    (h : ∀ x : {b // img R a b}, q (f x)) (hab : diag R a b) : q (f ⟨b, hab⟩) := by
  grind

example (R : α → α → Prop) (f : {b // img R a b} → β) (q : β → Prop)
    (h : ∀ x : {b // img R a b}, q (f x)) (hab : R a b) : q (f ⟨b, hab⟩) := by
  grind

example (s : α → Prop) (f : {b // mem s b} → β) (q : β → Prop)
    (h : ∀ x : {b // mem s b}, q (f x)) (hb : s b) : q (f ⟨b, hb⟩) := by
  grind

example (R : α → α → Prop) (f : {b // img R a b} → β) (q : β → Prop)
    (h : ∀ x : {b // img R a b}, q (f x)) (hab : R a b) (hne : ¬ q (f ⟨b, hab⟩)) : False := by
  grind

set_option linter.unusedVariables false

example (R : α → α → Prop) (f : {b // img R a b} → β) (hab : diag R a b) (h : f ⟨b, hab⟩ = c) :
    img R a b := by
  grind

example (R : α → α → Prop) (x : {b // img R a b}) (hab : diag R a b) (h : x = ⟨b, hab⟩) :
    img R a b := by
  grind

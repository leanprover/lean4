constant T : Type → Type
variables {α : Type}
def f : α → α := sorry
variables [decidable_eq α] {x y : T α}
axiom foo : true → f x = x
example : f x = x := by simp only [foo true.intro]
example : f x = x := by simp only [foo _]
example : f x = x := by simp [foo true.intro]
example : f x = x := by simp [foo _]

def g : α → α → α := sorry
variables [decidable_eq (T α)]
axiom bar : true → g x y = x
example : g x y = x := by simp [bar _]
example : g x y = x := by simp [bar true.intro]
example : g x y = x := by simp [bar]

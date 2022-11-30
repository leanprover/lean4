inductive Sublist : List α → List α → Prop
  | slnil : Sublist [] []
  | cons l₁ l₂ a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
  | cons2 l₁ l₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

#print Sublist

inductive Foo : List α → Type _  -- Make sure we don't need to use `_` or can use `u`
  | mk₁ : Foo []
  | mk₂ : (a : α) → Foo as → Foo (a::as)

inductive Bla : Foo as → Type _
  | mk₁ : Bla Foo.mk₁

#print Foo
#print Bla

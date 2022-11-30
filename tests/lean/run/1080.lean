inductive Foo
  | foo (f : Foo)

inductive Box
  | box (f : Foo)

def Box.foo : Box → Box
  | box f => box f.foo

inductive Bar : Box → Type
  | bar₁: Bar f → Bar f.foo
  | bar₂: Bar f → Bar f.foo

def Bar.Check : Bar f → Prop
  | bar₁ f => f.Check
  | bar₂ f => f.Check

attribute [simp] Bar.Check

#check Bar.Check._eq_1
#check Bar.Check._eq_2
#check Bar.Check.match_1.eq_1
#check Bar.Check.match_1.eq_2
#check Bar.Check.match_1.splitter

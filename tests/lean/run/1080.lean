inductive Foo
  | foo (f : Foo)

inductive Box
  | box (f: Foo)

def Box.foo: Box → Box
  | box f => box f.foo

inductive Bar: Box → Type
  | bar₁: Bar f → Bar f.foo
  | bar₂: Bar f → Bar f.foo

def Bar.check: Bar f → Prop
  | bar₁ f => f.check
  | bar₂ f => f.check

attribute [simp] Bar.check

#check Bar.check._eq_1
#check Bar.check._eq_2
#check Bar.check.match_1.eq_1
#check Bar.check.match_1.eq_2
#check Bar.check.match_1.splitter

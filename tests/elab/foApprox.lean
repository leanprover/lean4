def f : Prop → Prop := id

class Foo (foo : Prop → Prop) where
  l : x → foo x

instance : Foo f where
  l := by simp_all [f]

theorem test' (h : x = True) : f x := by
  have _ := True
  apply Foo.l  -- `?foo ?x =?= [mdata noImplicitLambda:1 f x]`
  simp [h]

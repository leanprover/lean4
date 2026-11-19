class Foo (d: Nat)
set_option checkBinderAnnotations false
inductive Bar [i: ∀ d', d ≤ d' → Foo d']
  | mk: Bar (i:=i)

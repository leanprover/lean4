class Foo (d: Nat)

inductive Bar [i: ∀ d', d ≤ d' → Foo d']
  | mk: Bar (i:=i)

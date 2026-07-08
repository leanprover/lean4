inductive Foo {f: Nat}: {d: Nat} → (h: d ≤ f) → Type where
| foo : Foo (Nat.zero_le _) → (Bool → Foo h) → Foo h

def Foo.bar (h: d ≤ f): Foo h → Foo h
| foo _ f => (f true).bar h

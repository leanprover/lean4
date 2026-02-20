inductive Foo : Nat → Type
| foo : Foo 0

inductive Bar: Foo n → Prop
| bar {t: Foo n} : (h : n = 0) → (h ▸ t) = .foo → Bar t

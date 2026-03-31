inductive Foo (n : Nat) : Type
| nil            : Foo n
| cons (s: Foo n): Foo n

namespace Foo

@[simp] def bar: {n: Nat} → Foo n → Foo n → Bool
| n+1, cons a, cons b => bar a b
| _, _, _ => true

example: bar (n:=n+1) nil nil = true := by
  simp only [bar]

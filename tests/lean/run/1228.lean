inductive Foo (n : Nat) : Type
| foo (t: Foo n): Foo n

namespace Foo
  inductive Bar: Foo n → Prop

  theorem ex₁ {s: Foo n} (H: s.Bar): True := by
    cases h₁ : s
    case foo s' =>
      cases h₂ : n; sorry
      have: Bar s' := sorry
      exact ex₁ this
  termination_by sizeOf s

  theorem ex₂
    {s: Foo n}
    (H: s.Bar):
    True := by
    generalize hs': s = s'
    match s' with
    | foo s' =>
      have: Bar s' := sorry
      have hterm: sizeOf s' < sizeOf s := by simp_all +arith
      exact ex₂ this
  termination_by sizeOf s

  theorem ex₃ {s: Foo n} (H: s.Bar): True := by
    cases h₁ : s
    case foo s' =>
      match n with
      | 0 => sorry
      | _ =>
        have: Bar s' := sorry
        exact ex₃ this
  termination_by sizeOf s

  -- it works
  theorem ex₄ {s: Foo n} (H: s.Bar): True := by
    match s with
    | foo s' =>
    match n with
    | 0 => sorry
    | _ =>
      have: Bar s' := sorry
      exact ex₄ this
  termination_by sizeOf s

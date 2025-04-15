inductive Impl where
  | inner (l r : Impl)
  | leaf

namespace Impl

inductive Balanced : Impl → Prop where
  | leaf : Balanced leaf

@[inline]
def balanceLErase (r : Impl) (hrb : Balanced r) : Impl :=
  match r with
  | leaf => .leaf
  | l@(inner _ _) =>
    match l with
    | leaf => .leaf
    | r@(inner ll lr) =>
        if true then
          match ll, lr with
          | inner _ _, inner _ _ => .leaf
          | _, _ => .leaf
        else .leaf

theorem size_balanceLErase {r : Impl} {hrb} : (balanceLErase r hrb) = .leaf := by
  simp only [balanceLErase]
  sorry

structure S :=
  (α : Type)
  (β : unit)

structure T (c : S)

structure U (c: S) (A : c^.α)

definition V (c : S) : S :=
{
  α := T c,
  β := by sorry
}

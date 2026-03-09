def optL (a : Option α) := if a = .none then 1 else 2
def optR (a : Option α) := if .none = a then 1 else 2

/-- info: 1 -/
#guard_msgs in #eval @optL Nat .none
/-- info: 2 -/
#guard_msgs in #eval optL (some ())
/-- info: 1 -/
#guard_msgs in #eval @optR Bool .none
/-- info: 2 -/
#guard_msgs in #eval optR (some 1.5)


-- test instance diamonds
example :
    @Option.decidableEqNone α none = @Option.decidableNoneEq α none := by
  with_reducible_and_instances rfl

section
variable {α : Type u} [DecidableEq α]
example (x : Option α) :
    Option.instDecidableEq x none = Option.decidableEqNone x := by
  with_reducible_and_instances rfl

example (x : Option α) :
    Option.instDecidableEq none x = Option.decidableNoneEq x := by
  with_reducible_and_instances rfl
end

def listL (a : List α) := if a = [] then 1 else 2
def listR (a : List α) := if [] = a then 1 else 2

/-- info: 1 -/
#guard_msgs in #eval @listL Nat []
/-- info: 2 -/
#guard_msgs in #eval listL [""]
/-- info: 1 -/
#guard_msgs in #eval @listL Nat []
/-- info: 2 -/
#guard_msgs in #eval listL [()]


-- test instance diamonds
example :
    @List.instDecidableEqNil α [] = @List.instDecidableNilEq α [] := by
  with_reducible_and_instances rfl

section
variable {α : Type u} [DecidableEq α]
example (x : List α) :
    instDecidableEqList x [] = List.instDecidableEqNil x := by
  with_reducible_and_instances rfl

example (x : List α) :
    instDecidableEqList [] x = List.instDecidableNilEq x := by
  with_reducible_and_instances rfl
end

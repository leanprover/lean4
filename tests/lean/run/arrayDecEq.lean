def listL (a : Array α) := if a = #[] then 1 else 2
def listR (a : Array α) := if #[] = a then 1 else 2

/-- info: 1 -/
#guard_msgs in #eval @listL Nat #[]
/-- info: 2 -/
#guard_msgs in #eval listL #[""]
/-- info: 1 -/
#guard_msgs in #eval @listL Nat #[]
/-- info: 2 -/
#guard_msgs in #eval listL #[()]


-- test instance diamonds
example :
    @Array.instDecidableEmpEq α #[] = @Array.instDecidableEqEmp α #[] := by
  with_reducible_and_instances rfl

section
variable {α : Type u} [DecidableEq α]
example (x : Array α) :
    Array.instDecidableEq x #[] = Array.instDecidableEqEmp x := by
  with_reducible_and_instances rfl

example (x : Array α) :
    Array.instDecidableEq #[] x = Array.instDecidableEmpEq x := by
  with_reducible_and_instances rfl
end

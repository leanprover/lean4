/-!
# Pretty printing shouldn't make use of "non-API exports"
-/

namespace A
def n : Nat := 22
end A

namespace B
export A (n)
end B

/-!
Was `B.n`
-/
/-- info: A.n : Nat -/
#guard_msgs in #check (A.n)

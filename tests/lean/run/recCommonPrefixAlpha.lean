namespace Structural
mutual
def f1 (α : Type) : List α → Nat
| [] => 0
| _ :: xs => f2 α xs + 1
termination_by structural n => n

-- NB β, not α. Used to prevent this from working (with an unhelpful error message)
def f2 (β : Type) : List β → Nat
| [] => 0
| _ :: xs => f1 β xs + 1
termination_by structural n => n
end
end Structural

namespace WF

mutual
def f1 (α : Type) : List α → Nat
| [] => 0
| _ :: xs => f2 α xs + 1
termination_by n => n

-- NB β, not α. Used to prevent this from working (with an unhelpful error message)
def f2 (β : Type) : List β → Nat
| [] => 0
| _ :: xs => f1 β xs + 1
termination_by n => n
decreasing_by
  -- NB: The proof goal for `f2` mentions `α`, not `β`. Could be fixed in theory if we really care
  guard_hyp α : Type
  decreasing_tactic
end
end WF

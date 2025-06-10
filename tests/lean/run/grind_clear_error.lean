reset_grind_attrs%
set_option grind.warning false

attribute [grind] List.not_mem_nil

/--
error: tactic 'grind' failed, the goal mentions the declaration `incList`, which is being defined. To avoid circular reasoning, try rewriting the goal to eliminate `incList` before using `grind`.
as✝ : List Nat
a : Nat
as : List Nat
⊢ ∀ (a : Nat), a ∈ (incList as).val → a > 0
-/
#guard_msgs (error) in
def incList (as : List Nat) : { as : List Nat // ∀ a, a ∈ as → a > 0 } :=
  match as with
  | [] => ⟨[], by grind⟩
  | a::as => ⟨(incList as).1, by grind⟩

/-- trace: [Compiler.specialize.info] pmap [N, N, O, H] -/
#guard_msgs in
set_option trace.Compiler.specialize.info true in
@[specialize]
def pmap : (l : List α) → (f : (a : α) → a ∈ l → β) → List β
  | [], _ => []
  | a :: l, f => f a List.mem_cons_self :: pmap l (fun a h => f a (List.mem_cons_of_mem _ h))

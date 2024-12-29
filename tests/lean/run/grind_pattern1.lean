set_option trace.grind.pattern true

/--
info: [grind.pattern] Array.getElem_push_lt: [@getElem ? `[Nat] #4 ? ? (@Array.push ? #3 #2) #1 ?]
-/
#guard_msgs in
grind_pattern Array.getElem_push_lt => (a.push x)[i]


/--
info: [grind.pattern] List.getElem_attach: [@getElem ? `[Nat] ? ? ? (@List.attach #3 #2) #1 ?]
-/
#guard_msgs in
grind_pattern List.getElem_attach => xs.attach[i]

/--
info: [grind.pattern] List.mem_concat_self: [@Membership.mem #2 ? ? (@HAppend.hAppend ? ? ? ? #1 (@List.cons ? #0 (@List.nil ?))) #0]
-/
#guard_msgs in
grind_pattern List.mem_concat_self => a ∈ xs ++ [a]

def foo (x : Nat) := x + x

/--
error: `foo` is not a theorem, you cannot assign patterns to non-theorems for the `grind` tactic
-/
#guard_msgs in
grind_pattern foo => x + x

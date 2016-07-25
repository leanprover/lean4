namespace smt
open tactic

meta_definition prove : tactic unit := trace_state >> now
end smt

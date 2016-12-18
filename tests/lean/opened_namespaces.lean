open nat
namespace foo
open int
run_command tactic.opened_namespaces >>= tactic.trace
end foo

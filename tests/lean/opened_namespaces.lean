open nat
namespace foo
open int
run_command tactic.open_namespaces >>= tactic.trace
end foo

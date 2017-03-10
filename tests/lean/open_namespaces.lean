open nat
namespace foo
open int
run_cmd tactic.open_namespaces >>= tactic.trace
end foo

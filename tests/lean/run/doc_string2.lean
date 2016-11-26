/-- Documentation for inductive foo -/
inductive foo
| val1 | val2

/-- Documentation for namespace foo -/
namespace foo
  /-- Documentation for x -/
  def x := 10
end foo

open tactic

run_command do
  namespace_doc_string `foo >>= trace,
  trace "--------",
  doc_string `foo >>= trace,
  trace "--------",
  doc_string `foo.x >>= trace

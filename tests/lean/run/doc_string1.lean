/--
Documentation for x

Testing...
-/
def x := 10 + 20

def y := "alo"

open tactic

run_command do
  d   ← doc_string `x,
  trace d

run_command add_doc_string `y "testing simple doc"

run_command do
  d   ← doc_string `y,
  trace d

/-- Documentation for foo -/
namespace foo
  /-- Documentation for bla -/
  namespace bla
  /-- Documentation for single -/
  inductive single
  | unit

  end bla
end foo

run_command do
  doc_string `foo >>= trace,
  doc_string `foo.bla >>= trace,
  doc_string `foo.bla.single >>= trace


/-- Documentation for constant A -/
constant A : Type

run_command doc_string `A >>= trace

/-- Documentation for point -/
structure point :=
(x : nat) (y : nat)

run_command doc_string `point >>= trace

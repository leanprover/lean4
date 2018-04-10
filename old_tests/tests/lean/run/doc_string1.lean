/--
Documentation for x

```
#reduce x + x
```
Testing...
-/
def x := 10 + 20

def y := "alo"

open tactic

run_cmd do
  d   ← doc_string `x,
  trace d

run_cmd add_doc_string `y "testing simple doc"

run_cmd do
  d   ← doc_string `y,
  trace d

namespace foo
  namespace bla
  /--
    Documentation for single
    testing...
     hello
      world
  -/
  inductive single
  | unit

  end bla
end foo

run_cmd do
  trace "--------",
  doc_string `foo.bla.single >>= trace


/-- Documentation for constant A
 foo -/
constant A : Type

run_cmd doc_string `A >>= trace

/--Documentation for point
test

 -/
structure point :=
(x : nat) (y : nat)

run_cmd doc_string `point >>= trace
#print "----------"

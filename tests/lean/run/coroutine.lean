import init.control.coroutine init.control.coroutine_io

universes u v
open coroutine

namespace ex1

inductive tree (α : Type u)
| leaf {} : tree
| node    : tree → α → tree → tree

/-- Coroutine as generators/iterators -/
def visit {α : Type v} : tree α → coroutine unit α unit
| tree.leaf         := pure ()
| (tree.node l a r) := do
  visit l,
  yield a,
  visit r

def tst {α : Type} [has_to_string α] (t : tree α) : except_t string io unit :=
do c  ← pure $ visit t,
   (yielded v₁ c) ← pure $ resume c (),
   (yielded v₂ c) ← pure $ resume c (),
   io.println $ to_string v₁,
   io.println $ to_string v₂,
   return ()

#eval tst (tree.node (tree.node (tree.node tree.leaf 5 tree.leaf) 10 (tree.node tree.leaf 20 tree.leaf)) 30 tree.leaf)

end ex1

namespace ex2

def ex : state_t nat (coroutine nat string) unit :=
do
  x ← read,
  y ← get,
  put (y+5),
  yield ("1) val: " ++ to_string (x+y)),
  x ← read,
  y ← get,
  yield ("2) val: " ++ to_string (x+y)),
  return ()

def tst2 : except_t string io unit :=
do let c := state_t.run ex 5,
   (yielded r c₁) ← pure $ resume c 10,
   io.println r,
   (yielded r c₂) ← pure $ resume c₁ 20,
   io.println r,
   (done _) ← pure $ resume c₂ 30,
   (yielded r c₃) ← pure $ resume c₁ 100,
   io.println r,
   io.println "done",
   return ()

#eval tst2

def ex3 : except_t string (coroutine_io nat string) unit :=
do
  x ← read,
  io.println $ "got " ++ to_string x,
  yield ("1) val: " ++ to_string x),
  x ← read,
  io.println $ "got " ++ to_string x,
  yield ("2) val: " ++ to_string x),
  throw "my_error"

open coroutine_io
def tst3 : except_t string io unit :=
do let c := ex3.run,
   (yielded r c₁) ← monad_lift $ c.resume 10,
   io.println r,
   (yielded r c₂) ← monad_lift $ c₁.resume 20,
   io.println r,
   (done (except.error e)) ← monad_lift $ c₂.resume 30,
   io.println $ "error: " ++ e,
   (yielded r c₃) ← monad_lift $ c₁.resume 100,
   io.println r,
   io.println "done",
   return ()

#eval tst3

end ex2

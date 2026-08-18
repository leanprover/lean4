import Lean
import Std

set_option backward.do.legacy false

open Lean Meta

structure Foo (n : Nat) where
  (l : List Nat)
  (h : n = n)

-- same as `foo` in #11337, except replacing `trace` by `logInfo`
def foo' (n : Nat) : MetaM Unit := do
  let mut result : Foo n := ⟨[7], rfl⟩
  logInfo m!"Initial value of result: {result.l}"
  result := ⟨List.range n, rfl⟩
  logInfo m!"We have a new value of result {result.l}"
  match n with
  | _ => logInfo m!"Now we keep the new value {result.l}"

/--
info: Initial value of result: [7]
---
info: We have a new value of result [0, 1, 2, 3, 4]
---
info: Now we keep the new value [0, 1, 2, 3, 4]
-/
#guard_msgs in
run_meta do
  foo' 5

local instance {α β cmp} [Append β] : Append (Std.TreeMap α β cmp) :=
  ⟨.mergeWith (fun _ ↦ (· ++ ·))⟩

def bar (hyp? : Option Unit) (a : α) : IO (Std.TreeMap Nat (Array α)) := do
  let mut tree := {}
  if true then
    pure ()
  tree := tree ++ (.insert {} 0 #[a])
  if let some _ := hyp? then
    tree := tree
  return tree

/-- info: Std.TreeMap.ofList [(0, #[3])] -/
#guard_msgs in
#eval bar none 3

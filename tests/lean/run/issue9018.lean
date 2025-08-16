-- set_option trace.Meta.sizeOf true
-- set_option trace.Meta.sizeOf.aux true

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs(pass trace, all) in
inductive Tree
  | node (children : List (id Tree))

/--
error: failed to generate `SizeOf` instance for `Nat'`:
  type mismatch
-/
#guard_msgs(pass trace, all) in
inductive Nat' -- type mismatch
  | zero
  | succ (n : id Nat')

/--
error: failed to generate `SizeOf` instance for `Tree₁`:
  failed to generate sizeOf theorem for Tree₁.node, (use `set_option genSizeOfSpec false` to disable theorem generation)
-/
#guard_msgs(pass trace, all) in
inductive Tree₁ -- failed to generate sizeOf theorem for Tree₁.node
  | node (children : List (Unit → id Tree₁))

/--
error: failed to generate `SizeOf` instance for `Tree₂`:
  failed to generate sizeOf theorem for Tree₂.node (use `set_option genSizeOfSpec false` to disable theorem generation), expected 'Nat.add' application, lhs is ⏎
    1
  rhs is
    1 + sizeOf head
-/
#guard_msgs(pass trace, all) in
inductive Tree₂ -- failed to generate sizeOf theorem for Tree₂.node
  | node (children : List ((fun α => α) Unit → Tree₂))

/--
error: failed to generate `SizeOf` instance for `Tree₃`:
  failed to generate sizeOf theorem for Tree₃.node, (use `set_option genSizeOfSpec false` to disable theorem generation)
-/
#guard_msgs(pass trace, all) in
inductive Tree₃ -- failed to generate sizeOf theorem for Tree₃.node
  | node (children : List (id (Unit → Tree₃)))


/--
error: failed to generate `SizeOf` instance for `Foo1`:
  type mismatch
-/
#guard_msgs(pass trace, all) in
inductive Foo1
| none
| some (v : Id Foo1)

structure Box (α : Type u) where
  data : α

-- ok
inductive Foo2
| none
| some (v : Box Foo2)

inductive BaseFoo (t : Type u -> Type v) (α : Type u)
| none
| some (v : t α)

/--
error: In argument #1 of constructor Foo3.mk:
  Invalid occurrence of inductive type `Foo3`, parameter #2 of `BaseFoo` is not positive.
  ⏎
  Note: That parameter is not positive:
    Non-positive occurrence of parameter `α` in type of BaseFoo.some, cannot nest through t
-/
#guard_msgs(pass trace, all) in
structure Foo3 where
  raw : BaseFoo Box Foo3

/--
error: In argument #1 of constructor Foo4.mk:
  Invalid occurrence of inductive type `Foo4`, parameter #2 of `BaseFoo` is not positive.
  ⏎
  Note: That parameter is not positive:
    Non-positive occurrence of parameter `α` in type of BaseFoo.some, cannot nest through t
-/
#guard_msgs(pass trace, all) in
structure Foo4 where
  raw : BaseFoo Id Foo4

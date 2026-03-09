class Foo

mutual
  inductive Bar [Foo] where
  inductive Baz [Foo] where -- Should not fail
end

/--
error: Invalid mutually inductive types: Parameter names `x` and `inst✝` differ but were expected to match
-/
#guard_msgs in
mutual
  inductive Bar1 [Foo] where
  inductive Baz1 [x : Foo] where -- Should fail
end


/--
error: Invalid mutually inductive types: Parameter names `β` and `α` differ but were expected to match
-/
#guard_msgs in
mutual
  inductive Boo (α : Type u) where
  inductive Bla (β : Type u) where
end

macro "gen_mutual" : command =>
  `(mutual
    inductive Boo (α : Type u) where
    inductive Bla (β : Type u) where
   end)

/--
error: unknown universe level `u✝`
---
error: unknown universe level `u✝`
---
error: Invalid mutually inductive types: Parameter names `β✝` and `α✝` differ but were expected to match
-/
#guard_msgs in
gen_mutual

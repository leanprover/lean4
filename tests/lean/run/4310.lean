class Foo

mutual
  inductive Bar [Foo] where
  inductive Baz [Foo] where -- Should not fail
end

/--
error: invalid mutually inductive types, parameter name mismatch 'x', expected 'inst✝'
-/
#guard_msgs in
mutual
  inductive Bar1 [Foo] where
  inductive Baz1 [x : Foo] where -- Should fail
end


/--
error: invalid mutually inductive types, parameter name mismatch 'β', expected 'α'
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
error: unknown universe level 'u✝'
---
error: unknown universe level 'u✝'
---
error: invalid mutually inductive types, parameter name mismatch 'β✝', expected 'α✝'
-/
#guard_msgs in
gen_mutual

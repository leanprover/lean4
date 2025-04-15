/-!
# Duplicate definition names in `mutual` blocks

https://github.com/leanprover/lean4/issues/6694

Definitions with conflicting names in `mutual` blocks should report errors rather than silently
failing or producing invalid entries in the environment.
-/

/--
error: 'mutual' block contains two declarations of the same name 'foo'
---
error: 'mutual' block contains two declarations of the same name 'foo'
-/
#guard_msgs in
mutual
def foo := ()

def foo := ()
end
/-- error: unknown identifier 'foo' -/
#guard_msgs in #check foo

/--
error: 'mutual' block contains two declarations of the same name 'foo'
---
error: 'mutual' block contains two declarations of the same name 'foo'
-/
#guard_msgs in
mutual
private def foo := ()

def foo := ()
end
/-- error: unknown identifier 'foo' -/
#guard_msgs in #check foo

/--
error: 'mutual' block contains two declarations of the same name 'y.z'
---
error: 'mutual' block contains two declarations of the same name 'y.z'
-/
#guard_msgs in
mutual
def y :=
  let rec z := 3
  z + 2

def y.z := 42
end
/-- error: unknown identifier 'y' -/
#guard_msgs in #check y
/-- error: unknown identifier 'y.z' -/
#guard_msgs in #check y.z

/--
error: 'mutual' block contains two declarations of the same name 'a.b'
---
error: 'mutual' block contains two declarations of the same name 'a.b'
-/
#guard_msgs in
mutual
def a :=
  b + 2
where b := 4

def a.b := 42
end
/-- error: unknown identifier 'a' -/
#guard_msgs in #check a
/-- error: unknown identifier 'a.b' -/
#guard_msgs in #check a.b

/--
error: cannot define an inductive type and a constructor with the same name 'Bar.foo'
---
error: cannot define an inductive type and a constructor with the same name 'Bar.foo'
-/
#guard_msgs in
mutual
  inductive Bar
  | foo : Bar

  inductive Bar.foo
  | mk : Bar.foo
end
/-- error: unknown identifier 'Bar' -/
#guard_msgs in #check Bar
/-- error: unknown identifier 'Bar.foo' -/
#guard_msgs in #check Bar.foo
/-- error: unknown identifier 'Bar.foo.mk' -/
#guard_msgs in #check Bar.foo.mk

/--
error: cannot define multiple inductive types with the same name 'Private'
---
error: cannot define multiple inductive types with the same name 'Private'
-/
#guard_msgs in
mutual
  private inductive Private
  | mk

  inductive Private
  | mk
end
/-- error: unknown identifier 'Private' -/
#guard_msgs in #check Private
/-- error: unknown identifier 'Private.mk' -/
#guard_msgs in #check Private.mk

/--
error: cannot define an inductive type and a constructor with the same name 'PrivateConstructor.priv'
---
error: cannot define an inductive type and a constructor with the same name 'PrivateConstructor.priv'
-/
#guard_msgs in
mutual
  inductive PrivateConstructor
  | private priv

  inductive PrivateConstructor.priv
  | mk
end
/-- error: unknown identifier 'PrivateConstructor' -/
#guard_msgs in #check PrivateConstructor
/-- error: unknown identifier 'PrivateConstructor.priv' -/
#guard_msgs in #check PrivateConstructor.priv

/--
error: cannot define multiple constructors with the same name 'Baz.foo.mk'
---
error: cannot define multiple constructors with the same name 'Baz.foo.mk'
-/
#guard_msgs in
mutual
  inductive Baz
  | foo.mk : Baz

  inductive Baz.foo
  | mk : Baz.foo
end
/-- error: unknown identifier 'Baz' -/
#guard_msgs in #check Baz
/-- error: unknown identifier 'Baz.foo' -/
#guard_msgs in #check Baz.foo
/-- error: unknown identifier 'Baz.foo.mk' -/
#guard_msgs in #check Baz.foo.mk

/--
error: cannot define multiple inductive types with the same name 'Foo'
---
error: cannot define multiple inductive types with the same name 'Foo'
-/
#guard_msgs in
mutual
  inductive Foo
  | bar : Foo

  inductive Foo
  | bar : Foo
  | foo : Foo → Foo
end
/-- error: unknown identifier 'Foo' -/
#guard_msgs in #check Foo
/-- error: unknown identifier 'Foo.bar' -/
#guard_msgs in #check Foo.bar
/-- error: unknown identifier 'Foo.foo' -/
#guard_msgs in #check Foo.foo

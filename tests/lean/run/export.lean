/-!
# Tests for the `export` command
-/

/-!
Explicit export
-/
def A.x : Bool := true
namespace B
export A (x)

/-- info: A.x : Bool -/
#guard_msgs in #check x
/-- info: x : Bool -/
#guard_msgs in #check (x)
end B

/-- info: A.x : Bool -/
#guard_msgs in #check B.x
/-- info: A.x : Bool -/
#guard_msgs in #check (B.x)


/-!
Namespace export
-/
namespace C
export A

/-- info: A.x : Bool -/
#guard_msgs in #check x
/-- info: x : Bool -/
#guard_msgs in #check (x)
end C

/-- info: A.x : Bool -/
#guard_msgs in #check C.x
/-- info: A.x : Bool -/
#guard_msgs in #check (C.x)


/-!
Renaming
-/
namespace D
export A renaming x → y

/-- info: A.x : Bool -/
#guard_msgs in #check y
/-- info: A.x : Bool -/
#guard_msgs in #check (y)
end D

/-- info: A.x : Bool -/
#guard_msgs in #check D.y
/-- info: A.x : Bool -/
#guard_msgs in #check (D.y)


/-!
Hiding
-/
def A.n : Nat := 0
namespace E
export A hiding x

/-- error: unknown identifier 'x' -/
#guard_msgs in #check x
/-- info: A.n : Nat -/
#guard_msgs in #check n
end E

/-- error: unknown identifier 'E.x' -/
#guard_msgs in #check E.x
/-- info: A.n : Nat -/
#guard_msgs in #check E.n


/-!
Protected export, atomic names don't resolve, but they still are accessible with `F.p` for example.
-/
protected def A.p : Bool := true
namespace F
export A (p)
/-- error: unknown identifier 'p' -/
#guard_msgs in #check p
/-- info: A.p : Bool -/
#guard_msgs in #check F.p
end F
/-- info: A.p : Bool -/
#guard_msgs in #check F.p

/-!
Exporting an inductive type
-/

inductive Foo where
  | cons

export Foo

/-- info: Foo.cons : Foo -/
#guard_msgs in #check cons
/-- error: unknown identifier 'recOn' -/
#guard_msgs in #check recOn

namespace G
export Foo
end G
/-- info: Foo.recOn.{u} {motive : Foo → Sort u} (t : Foo) (cons : motive cons) : motive t -/
#guard_msgs in #check G.recOn


/-!
Exporting a name, it also exports it as a namespace.
-/

inductive A.Ty where
  | mk

namespace H
export A (Ty)
end H
/-- info: A.Ty.mk : A.Ty -/
#guard_msgs in #check H.Ty.mk

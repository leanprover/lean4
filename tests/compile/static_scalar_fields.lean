/-!
Checks the scalar fields of constructor objects that the compiler emits as static data: the hash of
a name literal, a boxed `UInt64`, and the fields of structure literals whose scalars fill two 8-byte
chunks, after an object field or after an object field and a `USize` field, must agree with those
of the same values built at run time. The compiler writes each chunk with `LEAN_SCALAR_PTR_LITERAL`,
which must produce two slots on targets with 4-byte pointers (#15814). `simple_ground_extraction`
in `tests/elab` checks that the compiler emits values of these shapes as static data.
-/

structure Scalars where
  tag : String
  a : UInt64
  b : UInt32
  c : UInt16
  d : UInt8
deriving BEq

/-- A static object: `a` fills the first chunk, `b`, `c` and `d` the second. -/
def literal : Scalars :=
  { tag := "s", a := 0x0102030405060708, b := 0x090a0b0c, c := 0x0d0e, d := 0x0f }

structure WithUSize where
  tag : String
  u : USize
  a : UInt64
  b : UInt32
deriving BEq

/-- A static object whose chunks follow a `USize` slot. -/
def withUSize : WithUSize :=
  { tag := "u", u := 0x11121314, a := 0x2122232425262728, b := 0x31323334 }

/-- `some` of a boxed `UInt64`: a static object with one chunk and no other fields. -/
def boxed : Option UInt64 := some 0x4142434445464748

def main (args : List String) : IO Unit := do
  -- `args` is empty, but the compiler cannot know that, so these values are built at run time.
  let n := args.length
  let name := Lean.Name.mkStr (Lean.Name.mkStr .anonymous (args.getD 0 "foo")) "bar"
  IO.println s!"name hash: {(`foo.bar).hash == name.hash}"
  IO.println s!"name: {`foo.bar == name}"
  let scalars : Scalars := {
    tag := "s", a := 0x0102030405060708 + n.toUInt64, b := 0x090a0b0c + n.toUInt32,
    c := 0x0d0e + n.toUInt16, d := 0x0f + n.toUInt8 }
  IO.println s!"scalars: {literal == scalars}"
  let w : WithUSize := {
    tag := "u", u := 0x11121314 + n.toUSize, a := 0x2122232425262728 + n.toUInt64,
    b := 0x31323334 + n.toUInt32 }
  IO.println s!"with USize: {withUSize == w}"
  IO.println s!"boxed: {boxed == some (0x4142434445464748 + n.toUInt64)}"

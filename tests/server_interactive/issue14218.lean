-- Regression test for #14218: `open ... in <term>` should update the completion
-- context, so unqualified identifiers under the `open` complete against the opened
-- namespace(s). The first three variants match the ones in the issue; the fourth
-- exercises the analogous `set_option ... in <term>` case.

namespace Foo14218
opaque MyType : Type
axiom aParticularName : MyType
end Foo14218

-- Variant 1: no local `open`. Completion offers `Foo14218.aParticularName`, and the
-- item's `detail` uses the full type name `Foo14218.MyType`.
example : Foo14218.MyType :=
  aParticularNa
             --^ completion
#print ""

-- Variant 2: `open ... in <command>`. Completion offers `aParticularName` (short),
-- and `detail` shortens the type to `MyType`.
open Foo14218 in
example : Foo14218.MyType :=
  aParticularNa
             --^ completion
#print ""

-- Variant 3: `open ... in <term>`. Before the fix, the term elaborator did not push a
-- context node into the InfoTree, so the completion at the marker saw the outer
-- command's `openDecls` and offered the qualified name / qualified detail -- the bug
-- the issue reports. After the fix, this variant matches variant 2.
example : Foo14218.MyType :=
  open Foo14218 in
  aParticularNa
             --^ completion
#print ""

-- Variant 4: `set_option ... in <term>` under a term-level `open ... in`. Same class
-- of bug as variant 3 (the term-level `set_option` also did not push an InfoTree ctx
-- node). Inside the `set_option pp.fullNames true in`, the completion item's `detail`
-- should render the type fully qualified again (`Foo14218.MyType`) even though we
-- would otherwise be shortening under `open`.
example : Foo14218.MyType :=
  open Foo14218 in
  set_option pp.fullNames true in
  aParticularNa
             --^ completion
#print ""

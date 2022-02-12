--^ textDocument/foldingRange
import Lean
import Lean.Data

open Lean

namespace Foo

open Std
open Lean

section Bar

/-!
  A module-level doc comment
-/

/--
  Some documentation comment
-/
@[inline]
def add (x y : Nat) :=
  x + y

inductive InductiveTy
| a
|
  /--
    Another doc comment. This one is not folded.
  -/
  b

mutual
  def a :=
    1
  def b :=
    a
end

end Bar
end Foo

#check #[
  1,
  2,
  3
]

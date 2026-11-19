import Std.Internal.Parsec
open Std Internal Parsec String

/--
error: Cannot add `[macro_inline]` attribute to `f`: This attribute does not support this kind of declaration; only non-recursive definitions are supported
-/
#guard_msgs in
@[macro_inline] -- Error
def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n

/--
error: Cannot add `[macro_inline]` attribute to `g`: This attribute does not support this kind of declaration; only non-recursive definitions are supported
-/
#guard_msgs in
@[macro_inline] -- Error
def g : Nat → Nat
  | 0 => 0
  | n + 1 => g n
termination_by x => x

/--
error: Cannot add `[macro_inline]` attribute to `h._unary`: This attribute does not support this kind of declaration; only non-recursive definitions are supported
---
error: Cannot add `[macro_inline]` attribute to `h`: This attribute does not support this kind of declaration; only non-recursive definitions are supported
-/
#guard_msgs in
@[macro_inline] -- Error
def h : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => h n m
termination_by x y => x

/--
error: Cannot add `[macro_inline]` attribute to `i`: This attribute does not support this kind of declaration; only non-recursive definitions are supported
-/
#guard_msgs in
@[macro_inline] -- Error
def i : Nat → Nat
  | 0 => 0
  | n + 1 => i n
partial_fixpoint

/--
error: Cannot add `[macro_inline]` attribute to `skipMany`: This attribute does not support this kind of declaration; only non-recursive definitions are supported
-/
#guard_msgs in
@[macro_inline] -- Error
partial def skipMany (p : Parser α) (it : Sigma String.Pos) : Parser PUnit := do
  match p it with
  | .success it _ => skipMany p it
  | .error _ _  => pure ()

/-!
# Regression test for autoparam panic in `inductive` parameters

In the issue https://github.com/leanprover/lean4/issues/7788
there's an error that appears in these circumstances:
Given an `inductive` command whose header induces an autoparam,
and that autoparam has a metavariable in its type,
then there is a panic in `Expr.fvarId!`.

The problem came from not properly handling metavariables that appear in the parameter list,
which is how autoparams handle metavariables in their types (allowing them to be specialized later,
rather than committing to a free variable).
The fix was to be sure to abstract the parameters to create the type constructor types
(which incidentally simplified the handling of mutual inductives).
-/

set_option pp.mvars false

namespace Ex1

def const (a : A) (_ : B) := a

/-!
Here, `A` has an underdetermined type.
This results in two autoimplicits, one for `A` and one for its type.
-/
inductive X (h : const Unit A) where
  | a

/-- info: Ex1.X.{u_1} {x✝ : Sort u_1} {A : x✝} (h : const Unit A) : Type -/
#guard_msgs in #check X

/-!
Because `A` and its type are abstracted at header elaboration time,
it is too late to be able to specialize its type from within the constructor.
-/
/--
error: type expected, got
  (A : x✝)
-/
#guard_msgs in
inductive X' (h : const Unit A) where
  | a (x : A)

end Ex1

namespace Ex2

def const (a : A) (_ : B) := a

/-!
Make sure that `structure` can handle setting all the parameters to implicit
when processing default values.
(There used to be code that was conditional on a parameter being an fvar.)
-/
structure S (a : const Unit A) where
  x := a

/-- info: Ex2.S.x._default.{u_1} {x✝ : Sort u_1} {A : x✝} {a : const Unit A} : const Unit A -/
#guard_msgs in #check S.x._default

end Ex2

namespace Ex3
/-!
Example from issue #7788. Used to panic.
-/

/--
error: function expected at
  A
term has type
  ?_
-/
#guard_msgs in inductive X (h : A 1) where

end Ex3

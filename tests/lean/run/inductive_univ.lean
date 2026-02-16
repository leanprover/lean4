/-!
# Tests of universe constraint testing in the `inductive` command
-/

set_option pp.mvars false
set_option pp.universes true

/-!
Infers the resulting universe `Sort ?u`.
Here, `x : Nat : Type`, so `1 ≤ ?u` gives `Type` as least universe.
-/
inductive ExResultUni1 where
  | mk (x : Nat)
/--
info: inductive ExResultUni1 : Type
number of parameters: 0
constructors:
ExResultUni1.mk : Nat → ExResultUni1
-/
#guard_msgs in #print ExResultUni1

/-!
Infers the resulting universe `Sort ?u`.
Here, `x : α : Sort v`, so `v ≤ ?u` and the additional `1 ≤ ?u` gives `Sort (max 1 v)`.
-/
inductive ExResultUni2 (α : Sort v) where
  | mk (x : α)
/--
info: inductive ExResultUni2.{v} : Sort v → Sort (max 1 v)
number of parameters: 1
constructors:
ExResultUni2.mk : {α : Sort v} → α → ExResultUni2.{v} α
-/
#guard_msgs in #print ExResultUni2

/-!
Infers the resulting universe `Sort ?u`.
Here, `x : α : Type v`, so `v + 1 ≤ ?u`. The `1 ≤ ?u` isn't necessary. Get `Type v`.
-/
inductive ExResultUni3 (α : Type v) where
  | mk (x : α)
/--
info: inductive ExResultUni3.{v} : Type v → Type v
number of parameters: 1
constructors:
ExResultUni3.mk : {α : Type v} → α → ExResultUni3.{v} α
-/
#guard_msgs in #print ExResultUni3

/-!
Infers the resulting universe `Sort ?u`.
Even though this *could* be a syntactic subsingleton with `?u = 0`, it is recursive so, heuristically,
we don't use that solution.
From `x : α : Sort v` and `y : ExResultUni4 α : Sort ?u` we get `v ≤ ?u` and `?u ≤ ?u`.
With the additional `1 ≤ ?u`, we get `Sort (max 1 v)
-/
inductive ExResultUni4 (α : Sort v) where
  | mk (x : α) (y : ExResultUni4 α)
/--
info: inductive ExResultUni4.{v} : Sort v → Sort (max 1 v)
number of parameters: 1
constructors:
ExResultUni4.mk : {α : Sort v} → α → ExResultUni4.{v} α → ExResultUni4.{v} α
-/
#guard_msgs in #print ExResultUni4

/-!
An "unnecessarily high" universe warning. (Though erroneous!)
The use of `List` causes the resulting universe to be `Type ?u`.
From `x : α : Sort v` we get `v ≤ ?u + 1`, and from `y : List (ExResultUni5 α) : Type ?u` we get `?u ≤ ?u`.
There's a potential universe bump here, since ideally we would create `Type (v - 1)` as the level,
if there were such a thing as level subtraction, but instead the only solution is `Type v`.

Unfortunately, this check does not realize that `List (ExResultUni5 α)` forces `Type v`.
It's a warning, and it can be silenced with an explicit universe level.
-/
/--
warning: Inferred universe level for type may be unnecessarily high. The inferred resulting universe is
  Type v
but it possibly could be
  Sort (max 1 v)
Explicitly providing a resulting universe with no metavariables will silence this warning.

Note: The elaborated resulting universe after constructor elaboration is
  Type _
The inference algorithm attempts to compute the smallest level for `_` such that all universe constraints for all constructor fields are satisfied, with some approximations. The following derived constraint(s) are the cause of this possible unnecessarily high universe:
  v ≤ _+1
For example, if the resulting universe is of the form `Sort (?r + 1)` and a constructor field is in universe `Sort u`, the constraint `u ≤ ?r + 1` leads to the unnecessarily high resulting universe `Sort (u + 1)`. Using `Sort (max 1 u)` avoids this universe bump, if using it is possible.
-/
#guard_msgs in
inductive ExResultUni5 (α : Sort v) where
  | mk (x : α) (y : List (ExResultUni5 α))
-- Silenced:
#guard_msgs in
inductive ExResultUni5' (α : Sort v) : Type v where
  | mk (x : α) (y : List (ExResultUni5' α))

/--
Inference can handle `Sort (max _ 1)` as the resulting universe.
-/
inductive ExResultUni6 (α : Sort v) (β : Sort w) : Sort (max _ 1) where
  | mk (x : α) (y : β)
/-- info: ExResultUni6.{v, w} (α : Sort v) (β : Sort w) : Sort (max (max v w) 1) -/
#guard_msgs in #check ExResultUni6

/--
Inference can also handle parameters already existing in the resulting universe.
-/
inductive ExResultUni7 (α : Sort v) : Sort (max v _) where
  | mk (x : α)-- (n : Nat)
/-- info: ExResultUni7.{v} (α : Sort v) : Sort (max v 1) -/
#guard_msgs in #check ExResultUni7

/--
The universe of `α` is inferrable here, since it's known to be a `Type _` (from
the use of `List`), and inference will use level constraints to assign level metavariables
if they imply a unique solution, ignoring constant solutions if there's a non-constant solution.
-/
inductive ExParamUni1 (x : α) : Type v where
  | mk (ys : List α) (h : [x] = ys)
/--
info: inductive ExParamUni1.{v} : {α : Type v} → α → Type v
number of parameters: 2
constructors:
ExParamUni1.mk : {α : Type v} →
  {x : α} → (ys : List.{v} α) → Eq.{v + 1} (List.cons.{v} x List.nil.{v}) ys → ExParamUni1.{v} x
-/
#guard_msgs in #print ExParamUni1

/-!
Uses `Type v` for `α` and `β`, since these are the unique non-constant solutions.
-/
inductive ExParamUni2 {α β : Type _} (x : α) (y : β) : Type v where
  | mk (fs : List (α → β))
/--
info: inductive ExParamUni2.{v} : {α β : Type v} → α → β → Type v
number of parameters: 4
constructors:
ExParamUni2.mk : {α β : Type v} → {x : α} → {y : β} → List.{v} (α → β) → ExParamUni2.{v} x y
-/
#guard_msgs in #print ExParamUni2

/-!
The resulting type after resulting type inference is `Type ?u`, with a metavariable.
Constructor field universe propagation treats this metavariable as a parameter,
inferring `PUnit : Type ?u`.
-/
inductive ExParamUni3 {α : Type _} where
  | mk (x : α) (a : PUnit) -- use Unit if it should be in `Type 0`
/--
info: inductive ExParamUni3.{u_1} : {α : Type u_1} → Type u_1
number of parameters: 1
constructors:
ExParamUni3.mk : {α : Type u_1} → α → PUnit.{u_1 + 1} → ExParamUni3.{u_1}
-/
#guard_msgs in #print ExParamUni3

/-!
Given the resultant type, infer that the `x` parameter is `Type`.
-/
inductive T0 : Type where
  | mk (x : PUnit.{_+1})
/-- info: T0.mk (x : PUnit.{1}) : T0 -/
#guard_msgs in #check T0.mk

/-!
Given the resultant type, infer that the `x` parameter is `Type` as well.
-/
inductive T1 : Type where
  | mk (x : PUnit.{_+1} × PUnit.{_+1})
/-- info: T1.mk (x : Prod.{0, 0} PUnit.{1} PUnit.{1}) : T1 -/
#guard_msgs in #check T1.mk

/-!
Given the resultant type is `Prop`, do not do this inference.
-/
/--
error: Failed to infer universe levels in type of binder `x`
  Prod.{_, _} PUnit.{_ + 1} PUnit.{_ + 1}
-/
#guard_msgs in
inductive T3 : Prop where
  | mk (x : PUnit.{_+1} × PUnit.{_+1})

/-!
Given the resultant type, fail to infer a level for `PUnit` if there's not a unique solution.
-/
/--
error: Failed to infer universe levels in type of binder `x`
  PUnit.{_}
-/
#guard_msgs in
inductive E0 : Type 1 where
  | mk (x : PUnit)

/-!
Inference goes for `Type _` fields, so this succeeds.
-/
inductive E0' : Type where
  | mk (x : PUnit)

/-!
Given the resultant type, fail to infer a level for `PUnit` if there's not a unique solution.
-/
/--
error: Failed to infer universe levels in type of binder `x`
  Prod.{_, _} PUnit.{_ + 1} PUnit.{_ + 1}
-/
#guard_msgs in
inductive E1 : Type 1 where
  | mk (x : PUnit × PUnit)

/-!
Even though `α : Prop` is the unique solution, reject it for being unintuitive.
-/
/--
error: Failed to infer universe levels in type of binder `α`
  Sort _
-/
#guard_msgs in
inductive E2 : Type where
  | mk {α} (x : α)

/-!
`Sort` polymorphism is not allowed.
-/
/--
error: Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort u

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
-/
#guard_msgs in
inductive P (α : Sort u) : Sort u where
  | mk (x : α)

/-!
Errors for `structure` are specialized to talking about fields.
-/
/--
error: Invalid universe level for field `α`: Field has type
  Type
at universe level
  2
which is not less than or equal to the structure's resulting universe level
  1
-/
#guard_msgs in
structure A : Type where
  α : Type

/-!
Errors for `structure` talk about parent projection fields too.
(Note: it could easily point to `A'` and say the error is field `α`.)
-/
structure A' where
  α : Type
/--
error: Invalid universe level for field `α`: Field has type
  Type
at universe level
  2
which is not less than or equal to the structure's resulting universe level
  1
-/
#guard_msgs in
structure B : Type extends A'

/-!
Basic test of resulting type for recursive type.
Least universe is `Type`.
-/
inductive Bar3
| foobar {Foo : Prop} : Foo → Bar3
| somelist : List Bar3 → Bar3
/-- info: Bar3 : Type -/
#guard_msgs in #check Bar3

/-!
Test of resulting type for recursive type.
Least universe here is `Type 1`.
-/
inductive Bar4
| foobar {Foo : Type} : Foo → Bar4
| somelist : List Bar4 → Bar4
/-- info: Bar4 : Type 1 -/
#guard_msgs in #check Bar4

/-!
Like `Bar4`, but this time infers the type of the `Foo` field as `Type`.
-/
inductive Bar4' : Type 1
| foobar {Foo} : Foo → Bar4'
| somelist : List Bar4' → Bar4'
/-- info: Bar4' : Type 1 -/
#guard_msgs in #check Bar4'
/-- info: Bar4'.foobar {Foo : Type} : Foo → Bar4' -/
#guard_msgs in #check Bar4'.foobar

/-!
Type error at `List Bar5`, stops elaboration.
-/
/--
error: Application type mismatch: The argument
  Bar5
has type
  Prop
of sort `Type` but is expected to have type
  Type _
of sort `Type (_ + 1)` in the application
  List.{_} Bar5
-/
#guard_msgs in
inductive Bar5 : Prop where
| foobar {Foo : Prop} : Foo → Bar5
| somelist : List Bar5 → Bar5

/-!
Type error on `foobar` constructor. Resulting universe is too small.
-/
/--
error: Invalid universe level in constructor `Bar6.foobar`: Parameter `Foo` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#guard_msgs in
inductive Bar6 : Type where
| foobar {Foo : Type} : Foo → Bar6
| somelist : List Bar6 → Bar6

/-!
With `Foo : Prop`, the `Bar6` example would be ok.
-/
inductive Bar7 : Type where
| foobar {Foo : Prop} : Foo → Bar7
| somelist : List Bar7 → Bar7

/-!
While `Foo : Sort ?u` gives the constraint `?u + 1 ≤ 1`, which has `?u = 0` as the
unique solution, the `x : Foo : Sort ?u` gives the additional constraint `1 ≤ ?u`,
so it doesn't assign `?u = 0`.
-/
/--
error: Constructor field `Foo` of `Bar8.foobar` contains universe level metavariables at the expression
  Sort _
in its type
  Sort _
-/
#guard_msgs in
inductive Bar8 : Type where
| foobar : (x : Foo) → Bar8
| somelist : List Bar8 → Bar8

/-!
This gives `Foo : Type u`. This comes from `Foo : Sort ?u : Sort (?u + 1)`, so `?u + 1 ≤ u + 2`
has two non-constant solutions: `?u = u` and `?u = u + 1`.
Additionally, `x : Foo : Sort ?u` gives `1 ≤ ?u` since it's a field. This excludes `?u = u` since
`1 ≤ u` isn't always true.
Therefore it chooses `?u = u + 1`.
-/
inductive Bar9 : Type (u + 1) where
| foobar : (x : Foo) → Bar9
| somelist : List Bar9 → Bar9
/-- info: Bar9.foobar.{u} {Foo : Type u} (x : Foo) : Bar9.{u} -/
#guard_msgs in #check Bar9.foobar

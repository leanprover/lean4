import Lean
open Lean

inductive MyColor where
  | chartreuse | sienna | thistle

/--
error: failed to synthesize instance of type class
  Inhabited MyColor

Hint: Adding the command `deriving instance Inhabited for MyColor` may allow Lean to derive the missing instance.
-/
#guard_msgs in
def forceColor (oc : Option MyColor) :=
  oc.get!

/--
error: failed to synthesize instance of type class
  ToJson MyColor

Hint: Adding the command `deriving instance Lean.ToJson for MyColor` may allow Lean to derive the missing instance.
-/
#guard_msgs in
def jsonMaybeColor (oc : MyColor) :=
  ToJson.toJson oc

/--
error: failed to synthesize instance of type class
  ToJson MyColor

Hint: Adding the command `deriving instance Lean.ToJson for MyColor` may allow Lean to derive the missing instance.
---
error: failed to synthesize instance of type class
  ToExpr MyColor

Hint: Adding the command `deriving instance Lean.ToExpr for MyColor` may allow Lean to derive the missing instance.
---
error: No deriving handlers have been implemented for class `ToString`
-/
#guard_msgs in
inductive MyList where
  | nil : MyList
  | cons : MyColor → MyList
deriving ToJson, ToExpr, ToString, Nonempty


-- It would be very cool if this case could give us "maybe derive ToJson MyColor", but that's more sophisticated than we can presently manage
/--
error: failed to synthesize instance of type class
  ToJson (Option MyColor)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def jsonColor (oc : Option MyColor) :=
  ToJson.toJson oc

-- It would be very cool if this case could give us "maybe derive DecidableEq MyColor"
/--
error: failed to synthesize instance of type class
  Decidable (oc = some MyColor.thistle)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def checkColor (oc : Option MyColor) :=
  if oc = .some .thistle then 1 else 2

inductive MyTree where
  | nil : MyTree
  | cons : MyColor → MyTree → MyTree

-- The suggestion here will fail, it would be super awesome if we gave the full recommendation,
-- but each hint makes progress
/--
error: failed to synthesize instance of type class
  ToJson MyTree

Hint: Adding the command `deriving instance Lean.ToJson for MyTree` may allow Lean to derive the missing instance.
-/
#guard_msgs in
def jsonListColor (oc : MyTree) :=
  ToJson.toJson oc

/--
error: failed to synthesize instance of type class
  ToJson MyColor

Hint: Adding the command `deriving instance Lean.ToJson for MyColor` may allow Lean to derive the missing instance.
-/
#guard_msgs in
deriving instance Lean.ToJson for MyTree

deriving instance Lean.ToJson for MyColor

deriving instance Lean.ToJson for MyTree

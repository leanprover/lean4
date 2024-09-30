import Lean
/-!
# Make sure generated instance names are unique if there are macro scopes
-/

open Lean Elab Command

/-!
Example adapted from #2044
-/

#eval (do
  let stx ← `(
    structure Foo where
      field : String
    instance : Nonempty Foo := ⟨⟨"hi"⟩⟩)
  elabCommand stx
  : CommandElabM Unit
)

/-- error: unknown identifier 'instNonemptyFoo' -/
#guard_msgs in #check instNonemptyFoo

-- Verify that `instNonemptyFoo` is the name it would generate if it weren't hygienic

structure Foo where
  field : String
instance : Nonempty Foo := ⟨⟨"hi"⟩⟩

/-- info: instNonemptyFoo : Nonempty Foo -/
#guard_msgs in #check instNonemptyFoo

/-!
Example directly from #2044, deriving ToJson
-/

open Lean Elab Command
#eval (do
  let stx ← `(
    structure Foo where
      field : String
    deriving ToJson)
  elabCommand stx
  : CommandElabM Unit
)
/-- error: unknown identifier 'instToJsonFoo' -/
#guard_msgs in #check instToJsonFoo

deriving instance ToJson for Foo

/-- info: instToJsonFoo : ToJson Foo -/
#guard_msgs in #check instToJsonFoo


/-!
Can derive RpcEncodable multiple times in the same namespace.
-/

structure A1 where
  n : Nat
  deriving Lean.Server.RpcEncodable

structure A2 where
  n : Nat
  deriving Lean.Server.RpcEncodable

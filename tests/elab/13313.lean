module

-- Test that `deriving` inside a `public meta section` produces meta instances

public meta section

-- Delta deriving for definitions
@[expose] def Foo := Nat
deriving BEq

-- Meta definitions should be able to use the derived instance
def test (a b : Foo) : Bool := a == b

-- Standalone deriving instance for definitions
@[expose] def Bar := Nat
deriving instance Hashable for Bar

def testBar (a : Bar) : UInt64 := hash a

-- Handler-based deriving for inductives
inductive Baz where
  | a | b
deriving BEq, Repr, Hashable

def testBaz (x y : Baz) : Bool := x == y

-- DecidableEq for meta enums
inductive Qux where
  | x | y | z
deriving DecidableEq

def testDecEq (a b : Qux) : Bool := a == b

end

-- Outside any `meta section`: explicit `meta def` should also produce meta delta-derived instances.
-- This exercises the `isMarkedMeta (← getEnv) declName` branch in `processDefDeriving`.
public section

@[expose] meta def Quux := Nat
deriving BEq

meta def testQuux (a b : Quux) : Bool := a == b

end



inductive type
| bv  : Nat → type
| bit : type

open type

-- This is a "parameterized List" where `plist f types` contains
-- an element of Type `f tp` for each corresponding element `tp ∈ types`.
inductive plist (f : type → Type) : List type → Type
| nil {} : plist f []
| cons {h:type} {r:List type} : f h → plist f r → plist f (h::r)

-- Operations on values; the first argument contains the types of
-- inputs, and the second for the return Type.
inductive op : List type → type → Type
| neq (tp:type) : op [tp, tp] bit
| mul (w : Nat) : op [bv w, bv w] (bv w)

-- Denotes expressions that evaluate to a number given a memory State and register to value map.
inductive value : type → Type
| const (w : Nat) : value (bv w)
| op {args:List type} {tp:type} : op args tp → plist value args → value tp

--- This creates a plist (borrowed from the List notation).

open value

-- This works
-- #eval value.op (op.mul 32) [[[ const 32, const 32 ]]]

-- This also works
-- instance bvMul (w : Nat) : Mul (value (bv w)) := ⟨fun x y => w value.op (op.mul w) [[[x, y]]]⟩
-- #eval const 32 * const 32

-- This works
-- #eval value.op (op.neq (bv 32)) [[[ const 32, const 32 ]]]

-- def neq {tp:type} (x y : value tp) : value bit := value.op (op.neq tp) [[[x, y]]]
-- #eval neq (const 32) (const 32)

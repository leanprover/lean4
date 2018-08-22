inductive type
| bv  : ℕ → type
| bit : type

open type

-- This is a "parameterized list" where `plist f types` contains
-- an element of type `f tp` for each corresponding element `tp ∈ types`.
inductive plist (f : type → Type) : list type → Type
| nil {} : plist []
| cons {h:type} {r:list type} : f h → plist r → plist (h::r)

-- Operations on values; the first argument contains the types of
-- inputs, and the second for the return type.
inductive op : list type → type → Type
| neq (tp:type) : op [tp, tp] bit
| mul (w:ℕ) : op [bv w, bv w] (bv w)

-- Denotes expressions that evaluate to a number given a memory state and register to value map.
inductive value : type → Type
| const (w:ℕ) : value (bv w)
| op {args:list type} {tp:type} : op args tp → plist value args → value tp

--- This creates a plist (borrowed from the list notation).
notation `[[[` l:(foldr `,` (h t, plist.cons h t) plist.nil) `]]]` := l

open value

-- This works
#eval value.op (op.mul 32) [[[ const 32, const 32 ]]]

-- This also works
instance bv_has_mul (w:ℕ) : has_mul (value (bv w)) := ⟨λx y, value.op (op.mul w) [[[x, y]]]⟩
#eval const 32 * const 32

-- This works
#eval value.op (op.neq (bv 32)) [[[ const 32, const 32 ]]]

-- This returns the VM check error
def neq {tp:type} (x y : value tp) : value bit := value.op (op.neq tp) [[[x, y]]]
#eval neq (const 32) (const 32)


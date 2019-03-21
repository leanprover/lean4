inductive Type
| bv  : ℕ → Type
| bit : Type

open Type

-- This is a "parameterized List" where `plist f types` contains
-- an element of Type `f tp` for each corresponding element `tp ∈ types`.
inductive plist (f : Type → Type) : List Type → Type
| nil {} : plist []
| cons {h:Type} {r:List Type} : f h → plist r → plist (h::r)

-- Operations on values; the first argument contains the types of
-- inputs, and the second for the return Type.
inductive op : List Type → Type → Type
| neq (tp:Type) : op [tp, tp] bit
| mul (w:ℕ) : op [bv w, bv w] (bv w)

-- Denotes expressions that evaluate to a number given a memory State and register to value map.
inductive value : Type → Type
| const (w:ℕ) : value (bv w)
| op {args:List Type} {tp:Type} : op args tp → plist value args → value tp

--- This creates a plist (borrowed from the List notation).
notation `[[[` l:(foldr `,` (h t, plist.cons h t) plist.nil) `]]]` := l

open value

-- This works
#eval value.op (op.mul 32) [[[ const 32, const 32 ]]]

-- This also works
instance bvHasMul (w:ℕ) : HasMul (value (bv w)) := ⟨λx y, value.op (op.mul w) [[[x, y]]]⟩
#eval const 32 * const 32

-- This works
#eval value.op (op.neq (bv 32)) [[[ const 32, const 32 ]]]

-- This returns the VM check error
def neq {tp:Type} (x y : value tp) : value bit := value.op (op.neq tp) [[[x, y]]]
#eval neq (const 32) (const 32)


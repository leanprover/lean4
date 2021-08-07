def Sequence (α : Type) := List α

def BigBody (β α) :=  α × (β → β → β) × Bool × β

def applyBig {α β : Type} (body : BigBody β α) (x : β) : β :=
let (_, op, b, v) := body;
if b then op v x else x

def reducebig {α β : Type} (idx : β) (r : Sequence α) (body : α → BigBody β α) : β :=
r.foldr (applyBig ∘ body) idx

def bigop := @reducebig

partial def iota : Nat → Nat → List Nat
| m, 0   => []
| m, n+1 => m :: iota (m+1) n

def index_iota (m n : Nat) := iota m (n - m)

class Enumerable (α : Type) :=
(elems {} : List α)

instance : Enumerable Bool :=
{ elems := [false, true] }

-- instance {α β} [Enumerable α] [Enumerable β]: Enumerable (α × β) :=
-- { elems := do let a ← Enumerable.elems α; let b ← Enumerable.elems β; pure (a, b) }

partial def finElemsAux (n : Nat) : (i : Nat) → i < n → List (Fin n)
| 0,   h => [⟨0, h⟩]
| i+1, h => ⟨i+1, h⟩ :: finElemsAux n i (Nat.lt_of_succ_lt h)

partial def finElems : (n : Nat) → List (Fin n)
| 0     => []
| (n+1) => finElemsAux (n+1) n (Nat.lt_succ_self n)

instance {n} : Enumerable (Fin n) :=
{ elems := (finElems n).reverse }

instance : OfNat (Fin (Nat.succ n)) m :=
⟨Fin.ofNat m⟩

-- Declare a new syntax category for "indexing" big operators
declare_syntax_cat index
syntax term:51 "≤" ident "<" term : index
syntax term:51 "≤" ident "<" term "|" term : index
syntax ident "<-" term : index
syntax ident "<-" term "|" term : index
-- Primitive notation for big operators
syntax "_big" "[" term "," term "]" "(" index ")" term : term

-- We define how to expand `_bigop` with the different kinds of index
macro_rules
| `(_big [$op, $idx] ($i:ident <- $r | $p) $F) => `(bigop $idx $r (fun $i:ident => ($i:ident, $op, $p, $F)))
| `(_big [$op, $idx] ($i:ident <- $r) $F) => `(bigop $idx $r (fun $i:ident => ($i:ident, $op, true, $F)))
| `(_big [$op, $idx] ($lower:term ≤ $i:ident < $upper) $F) => `(bigop $idx (index_iota $lower $upper) (fun $i:ident => ($i:ident, $op, true, $F)))
| `(_big [$op, $idx] ($lower:term ≤ $i:ident < $upper | $p) $F) => `(bigop $idx (index_iota $lower $upper) (fun $i:ident => ($i:ident, $op, $p, $F)))

-- Define `Sum`
syntax "Sum" "(" index ")" term : term
macro_rules | `(Sum ($idx) $F) => `(_big [Add.add, 0] ($idx) $F)

-- We can already use `Sum` with the different kinds of index.
#check Sum (i <- [0, 2, 4] | i != 2) i
#check Sum (10 ≤ i < 20 | i != 5) i+1
#check Sum (10 ≤ i < 20) i+1

-- Define `Prod`
syntax "Prod" "(" index ")" term : term
macro_rules | `(Prod ($idx) $F) => `(_big [Mul.mul, 1] ($idx) $F)

-- The examples above now also work for `Prod`
#check Prod (i <- [0, 2, 4] | i != 2) i
#check Prod (10 ≤ i < 20 | i != 5) i+1
#check Prod (10 ≤ i < 20) i+1

-- We can extend our grammar for the syntax category `index`.
syntax ident "|" term : index
syntax ident ":" term : index
syntax ident ":" term "|" term : index
-- And new rules
macro_rules
| `(_big [$op, $idx] ($i:ident : $type) $F) => `(bigop $idx (Enumerable.elems $type) (fun $i:ident => ($i:ident, $op, true, $F)))
| `(_big [$op, $idx] ($i:ident : $type | $p) $F) => `(bigop $idx (Enumerable.elems $type) (fun $i:ident => ($i:ident, $op, $p, $F)))
| `(_big [$op, $idx] ($i:ident | $p) $F) => `(bigop $idx (Enumerable.elems _) (fun $i:ident => ($i:ident, $op, $p, $F)))

-- The new syntax is immediately available for all big operators that we have defined
def myPred (x : Fin 10) : Bool := true
#check Sum (i : Fin 10) i+1
#check Sum (i : Fin 10 | i != 2) i+1
#check Sum (i | myPred i) i+i
#check Prod (i : Fin 10) i+1
#check Prod (i : Fin 10 | i != 2) i+1
#check Prod (i | myPred i) i+i

-- We can easily create alternative syntax for any big operator.
syntax "Σ" index "=>" term : term
macro_rules | `(Σ $idx => $F) => `(Prod ($idx) $F)

#check Σ 10 ≤ i < 20 => i+1

-- Now, we create command for automating the generation of big operators.
syntax "def_bigop" str term:max term:max : command
macro_rules
| `(def_bigop $head:strLit $op $unit) =>
   `(macro $head:strLit "(" idx:index ")" F:term : term => `(_big [$op, $unit] ($$idx) $$F))

def_bigop "SUM" Nat.add 0
#check SUM (i <- [0, 1, 2]) i+1

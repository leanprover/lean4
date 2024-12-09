abbrev Sequence (α : Type) := List α

def bigop (init : β) (seq : Sequence α) (op : β → β → β) (f : α → Bool × β) : β := Id.run do
  let mut result := init
  for a in seq do
    let (ok, b) := f a
    if ok then
      result := op result b
  return result

#eval bigop 0 [1, 2, 4] Add.add fun elem => (elem % 2 == 0, elem * 2)

def iota : Nat → Nat → List Nat
  | _, 0   => []
  | m, n+1 => m :: iota (m+1) n

def index_iota (m n : Nat) := iota m (n - m)

class Enumerable (α : Type) where
  elems : List α

instance : Enumerable Bool where
  elems := [false, true]

instance {α β} [Enumerable α] [Enumerable β]: Enumerable (α × β) where
  elems := Enumerable.elems.bind fun (a : α) => Enumerable.elems.bind fun (b : β) => [(a, b)]

def finElems (n : Nat) : List (Fin n) :=
  match n with
  | 0   => []
  | n+1 => go (n+1) n (by simp_arith)
where
  go (n : Nat) (i : Nat) (h : i < n) : List (Fin n) :=
   match i with
   | 0 => [⟨0, h⟩]
   | i+1 => ⟨i+1, h⟩ :: go n i (Nat.lt_of_succ_lt h)

instance : Enumerable (Fin n) where
  elems := (finElems n).reverse

instance : OfNat (Fin (Nat.succ n)) m :=
  ⟨Fin.ofNat' _ m⟩

-- Declare a new syntax category for "indexing" big operators
declare_syntax_cat index
syntax term:51 "≤" ident "<" term : index
syntax term:51 "≤" ident "<" term "|" term : index
syntax ident "<-" term : index
syntax ident "<-" term "|" term : index
-- Primitive notation for big operators
syntax "_big" "[" term "," term "]" "(" index ")" term : term

-- We define how to expand `_big` with the different kinds of index
macro_rules
| `(_big [$op, $idx] ($i:ident <- $r | $p) $F) => `(bigop $idx $r $op (fun $i:ident => ($p, $F)))
| `(_big [$op, $idx] ($i:ident <- $r) $F) => `(bigop $idx $r $op (fun $i:ident => (true, $F)))
| `(_big [$op, $idx] ($lower:term ≤ $i:ident < $upper) $F) => `(bigop $idx (index_iota $lower $upper) $op (fun $i:ident => (true, $F)))
| `(_big [$op, $idx] ($lower:term ≤ $i:ident < $upper | $p) $F) => `(bigop $idx (index_iota $lower $upper) $op (fun $i:ident => ($p, $F)))

-- Define `∑ `
syntax "∑ " "(" index ")" term : term
macro_rules | `(∑ ($idx) $F) => `(_big [Add.add, 0] ($idx) $F)

-- We can already use `Sum` with the different kinds of index.
#check ∑ (i <- [0, 2, 4] | i != 2) i
#check ∑ (10 ≤ i < 20 | i != 5) i+1
#check ∑ (10 ≤ i < 20) i+1

-- Define `∏`
syntax "∏" "(" index ")" term : term
macro_rules | `(∏ ($idx) $F) => `(_big [Mul.mul, 1] ($idx) $F)

-- The examples above now also work for `Prod`
#check ∏ (i <- [0, 2, 4] | i != 2) i
#check ∏ (10 ≤ i < 20 | i != 5) i+1
#check ∏ (10 ≤ i < 20) i+1

-- We can extend our grammar for the syntax category `index`.
syntax ident "|" term : index
syntax ident ":" term : index
syntax ident ":" term "|" term : index
-- And new rules
macro_rules
| `(_big [$op, $idx] ($i:ident : $type) $F) => `(bigop $idx (Enumerable.elems (α := $type)) $op (fun $i:ident => (true, $F)))
| `(_big [$op, $idx] ($i:ident : $type | $p) $F) => `(bigop $idx (Enumerable.elems (α := $type)) $op (fun $i:ident => ($p, $F)))
| `(_big [$op, $idx] ($i:ident | $p) $F) => `(bigop $idx (Enumerable.elems) $op (fun $i:ident => ($p, $F)))

-- The new syntax is immediately available for all big operators that we have defined
def myPred (x : Fin 10) : Bool := true
#check ∑ (i : Fin 10) i+1
#check ∑ (i : Fin 10 | i != 2) i+1
#check ∑ (i | myPred i) i+i
#check ∏ (i : Fin 10) i+1
#check ∏ (i : Fin 10 | i != 2) i+1
#check ∏ (i | myPred i) i+i

-- We can easily create alternative syntax for any big operator.
syntax "Summation" index "=>" term : term
macro_rules | `(Summation $idx => $F) => `(∑ ($idx) $F)

#check Summation 10 ≤ i < 20 => i+1

-- Now, we create command for automating the generation of big operators.
syntax "def_bigop" str term:max term:max : command
macro_rules
| `(def_bigop $head:str $op $unit) =>
   `(macro $head:str "(" idx:index ")" F:term : term => `(_big [$op, $unit] ($$idx) $$F))

def_bigop "SUM" Nat.add 0
#check SUM (i <- [0, 1, 2]) i+1

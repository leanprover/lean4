def Seq (α : Type) := List α

def BigBody (β α) :=  α × (β → β → β) × Bool × β

def applyBig {α β : Type} (body : BigBody β α) (x : β) : β :=
let (_, op, b, v) := body;
if b then op v x else x

def reducebig {α β : Type} (idx : β) (r : Seq α) (body : α → BigBody β α) : β :=
r.foldr (applyBig ∘ body) idx

def bigop := @reducebig

def iota : Nat → Nat → List Nat
| m, 0   => []
| m, n+1 => m :: iota (m+1) n

def index_iota (m n : Nat) := iota m (n - m)

new_frontend

declare_syntax_cat index

syntax ident "|" term : index
syntax term:50 "≤" ident "<" term : index
syntax term:50 "≤" ident "<" term "|" term : index
syntax ident "<-" term : index
syntax ident "<-" term "|" term : index

syntax "_big" "[" term "," term "]" "(" index ")" term : term

macro_rules
| `(_big [ $op , $idx ] ( $i:ident <- $r | $p ) $F) => `(bigop $idx $r (fun $i:ident => ($i:ident, $op, $p, $F)))
| `(_big [ $op , $idx ] ( $i:ident <- $r ) $F) => `(bigop $idx $r (fun $i:ident => ($i:ident, $op, true, $F)))
| `(_big [ $op , $idx ] ( $lower ≤ $i:ident < $upper ) $F) => `(bigop $idx (index_iota $lower $upper) (fun $i:ident => ($i:ident, $op, true, $F)))
| `(_big [ $op , $idx ] ( $lower ≤ $i:ident < $upper | $p ) $F) => `(bigop $idx (index_iota $lower $upper) (fun $i:ident => ($i:ident, $op, $p, $F)))

syntax "Sum" "(" index ")" term : term

macro_rules
| `(Sum ($idx:index) $F:term) => `(_big [Nat.add, 0] ($idx:index) $F:term)

syntax "Prod" "(" index ")" term : term

macro_rules
| `(Prod ($idx:index) $F:term) => `(_big [Nat.mul, 1] ($idx:index) $F:term)

#check Sum (i <- [0, 2, 4] | i != 2) i
#check Sum (10 ≤ i < 20 | i != 5) (i+1)
#check Sum (10 ≤ i < 20) (i+1)
#check Prod (i <- [0, 2, 4] | i != 2) i
#check Prod (10 ≤ i < 20 | i != 5) (i+1)
#check Prod (10 ≤ i < 20) (i+1)
#check Prod (10 ≤ i < 20) (i+1)

syntax "Prod" index "=>" term : term

macro_rules
| `(Prod $idx:index => $F:term) => `(Prod ($idx:index) $F)

#check Prod 10 ≤ i < 20 => i+1

syntax "def_bigop" str term:max term:max : command

macro_rules
| `(def_bigop $head:strLit $op $unit) =>
   -- We have to use `$(mkAntiquotStx idx "index"):index` instead of `$idx:index` because it occurs inside of a nested quasiquotation.
   -- We have to use write `(HasBind.bind `(idx) (fund idx => ...))` to make sure `idx` contains the same macro scopes of the `idx` occurring
   -- on the left-hand-side of the macro command.
   HasBind.bind `(idx) (fun idx => HasBind.bind `(F) (fun F =>
    `(macro $head:strLit "(" idx:index ")" F:term : term => `(_big [$op, $unit] ($(idx.termIdToAntiquot "index"):index) $(F.termIdToAntiquot "term")))))

def_bigop "S" Nat.add 0

#check S (i <- [0, 1, 2]) (i+1)

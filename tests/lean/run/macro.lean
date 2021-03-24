abbrev Set (α : Type) := α → Prop
axiom setOf {α : Type} : (α → Prop) → Set α
axiom mem {α : Type} : α → Set α → Prop
axiom univ {α : Type} : Set α
axiom Union {α : Type} : Set (Set α) → Set α

syntax:100 term " ∈ " term:99 : term

macro_rules
| `($x:term ∈ $s:term) => `(mem $x:term $s:term)

declare_syntax_cat index

syntax term : index
syntax term "≤" ident "<" term : index
syntax ident ":" term : index

syntax "{" index " | " term "}" : term

macro_rules
-- | `({ $l:term ≤ $x:ident < $u:term | $p:term }) => `(setOf (fun $x:ident => $l:term ≤ $x:ident ∧ $x:ident < $u:term ∧ $p:term))
| `({ $x:ident : $t:term | $p:term }) => `(setOf (fun ($x:ident : $t:term) => $p:term))
| `({ $x:term ∈ $s:term | $p:term }) => `(setOf (fun $x:term => $x:term ∈ $s:term ∧ $p:term))
| `({ $x:term ≤ $e:term | $p:term }) => `(setOf (fun $x:term => $x:term ≤ $e:term ∧ $p:term))
| `({ $b:term | $r:term}) => `(setOf (fun $b:term => $r:term))

-- #check { 1 ≤ x < 10 | x ≠ 5 }
#check { f : Nat → Nat | f 1  > 0 }

syntax "⋃ " term ", " term : term

macro_rules
| `(⋃ $b:term, $r:term) => `(Union {$b:term | $r:term})

#check ⋃ x,              x = x
#check ⋃ (x : Set Unit), x = x
#check ⋃ x ∈ univ,       x = x

syntax "#check2" term : command

macro_rules
| `(#check2 $e) => `(#check $e #check $e)

#check2 1

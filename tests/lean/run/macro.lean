abbrev Set (α : Type) := α → Prop
axiom setOf {α : Type} : (α → Prop) → Set α
axiom mem {α : Type} : α → Set α → Prop
axiom univ {α : Type} : Set α
axiom Union {α : Type} : Set (Set α) → Set α

new_frontend

syntax term " ∈ ":100 term:99 : term

macro_rules
| `($x ∈ $s) => `(mem $x $s)

declare_syntax_cat index

syntax term : index
syntax term "≤" ident "<" term : index
syntax ident ":" term : index

syntax "{" index " | " term "}" : term

-- #check { x : Nat → Nat | x > 0 }

-- set_option trace.Elab true
-- set_option syntaxMaxDepth 6

macro_rules
| `({$l ≤ $x:ident < $u | $p}) => `(setOf (fun $x:ident => $l ≤ $x:ident ∧ $x:ident < $u ∧ $p))
-- | `({$x:ident : $t | $p}) => `(setOf (fun ($x:ident : $t) => $p))
| `({$x ∈ $s | $p}) => `(setOf (fun $x => $x ∈ $s ∧ $p))
| `({$x ≤ $e | $p}) => `(setOf (fun $x => $x ≤ $e ∧ $p))
| `({$b      | $r}) => `(setOf (fun $b => $r))

#check { 1 ≤ x < 10 | x ≠ 5 }

syntax "⋃ " term ", " term : term

macro_rules
| `(⋃ $b, $r) => `(Union {$b | $r})

#check ⋃ x,              x = x
#check ⋃ (x : Set Unit), x = x
#check ⋃ x ∈ univ,       x = x

syntax "#check2" term : command

macro_rules
| `(#check2 $e) => `(#check $e #check $e)

#check2 1

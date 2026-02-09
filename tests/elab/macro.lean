set_option pp.mvars false

namespace Test

abbrev Set (α : Type) := α → Prop
axiom setOf {α : Type} : (α → Prop) → Set α
axiom mem {α : Type} : α → Set α → Prop
axiom univ {α : Type} : Set α
axiom Union {α : Type} : Set (Set α) → Set α

syntax:100 (priority := high) term " ∈ " term:99 : term

macro_rules
| `($x ∈ $s) => `(mem $x $s)

declare_syntax_cat index

syntax term : index
-- `≤` has precedence 50
syntax term:51 "≤" ident "<" term:51 : index
syntax ident ":" term : index

syntax "{" index " | " term "}" : term

macro_rules
| `({$l:term ≤ $x < $u | $p}) => `(setOf (fun $x => $l ≤ $x ∧ $x < $u ∧ $p))
| `({$x:ident : $t | $p}) => `(setOf (fun ($x : $t) => $p))
| `({$x:term ∈ $s | $p}) => `(setOf (fun $x => $x ∈ $s ∧ $p))
| `({$x:term ≤ $e | $p}) => `(setOf (fun $x => $x ≤ $e ∧ $p))
| `({$b:term      | $r}) => `(setOf (fun $b => $r))

/-- info: setOf fun x => 1 ≤ x ∧ x < 10 ∧ x ≠ 5 : Set Nat -/
#guard_msgs in
#check { 1 ≤ x < 10 | x ≠ 5 }

/-- info: setOf fun f => f 1 > 0 : Set (Nat → Nat) -/
#guard_msgs in
#check { f : Nat → Nat | f 1  > 0 }

syntax "⋃ " term ", " term : term

macro_rules
| `(⋃ $b, $r) => `(Union {$b:term | $r})

/-- info: Union (setOf fun x => x = x) : Set ?_ -/
#guard_msgs in
#check ⋃ x,              x = x

/-- info: Union (setOf fun x => x = x) : Set Unit -/
#guard_msgs in
#check ⋃ (x : Set Unit), x = x

/-- info: Union (setOf fun x => mem x univ ∧ x = x) : Set ?_ -/
#guard_msgs in
#check ⋃ x ∈ univ,       x = x

syntax "#check2" term : command

macro_rules
| `(#check2 $e) => `(#check $e #check $e)

/--
info: 1 : Nat
---
info: 1 : Nat
-/
#guard_msgs in
#check2 1

end Test

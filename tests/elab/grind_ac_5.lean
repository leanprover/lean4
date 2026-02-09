/--
error: `grind` failed
case grind
a b c d e f : Nat
h : max a b = max c d
h_1 : max b e = max d (max e f)
h_2 : ¬max c (max d e) = max (max a d) f
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] max a b = max c d
    [prop] max b e = max d (max e f)
    [prop] ¬max c (max d e) = max (max a d) f
  [eqc] False propositions
    [prop] max c (max d e) = max (max a d) f
  [eqc] Equivalence classes
    [eqc] {max a b, max c d}
    [eqc] {max b e, max d (max e f)}
  [assoc] Operator `max`
    [basis] Basis
      [_] max c d = max a b
      [_] max b (max c e) = max a (max b e)
      [_] max b (max e f) = max b e
      [_] max b (max d e) = max b e
      [_] max d (max e f) = max b e
      [_] max a (max b d) = max a b
      [_] max a (max b c) = max a b
    [diseqs] Disequalities
      [_] max a (max b e) ≠ max a (max d f)
    [properties] Properties
      [_] commutative
      [_] idempotent
      [_] identity: `0`
-/
#guard_msgs in
example (a b c d e f : Nat) :
    max a b = max c d →
    max b e = max d (max e f) →
    max c (max d e) = max (max a d) f := by
  grind -lia only

/--
error: `grind` failed
case grind
α : Sort u
op : α → α → α
inst : Std.Associative op
a b c d : α
h : op a b = op c d
h_1 : ¬op (op a b) (op b c) = op (op c d) c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] Std.Associative op
    [prop] op a b = op c d
    [prop] ¬op (op a b) (op b c) = op (op c d) c
  [eqc] True propositions
    [prop] Std.Associative op
  [eqc] False propositions
    [prop] op (op a b) (op b c) = op (op c d) c
  [eqc] Equivalence classes
    [eqc] {op (op a b), op (op c d)}
    [eqc] {op a b, op c d}
  [assoc] Operator `op`
    [basis] Basis
      [_] op c d = op a b
    [diseqs] Disequalities
      [_] op a (op b (op b c)) ≠ op a (op b c)
-/
#guard_msgs in
example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
    : op a b = op c d → op (op a b) (op b c) = op (op c d) c := by
  grind only

set_option warn.sorry false
set_option grind.debug true

opaque op : Int → Int → Int
instance : Std.Associative op := sorry
instance : Std.Commutative op := sorry
local infixr:64 "∘" => op

/--
error: `grind` failed
case grind
a b c d e p q : Int
h : a∘b = c∘d
h_1 : a∘q = p
h_2 : ¬(c∘d)∘e = a∘p∘q
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a∘b = c∘d
    [prop] a∘q = p
    [prop] ¬(c∘d)∘e = a∘p∘q
  [eqc] False propositions
    [prop] (c∘d)∘e = a∘p∘q
  [eqc] Equivalence classes
    [eqc] {p, a∘q}
    [eqc] {a∘b, c∘d}
  [assoc] Operator `op`
    [basis] Basis
      [_] a∘q = p
      [_] c∘d = a∘b
    [diseqs] Disequalities
      [_] a∘b∘e ≠ p∘p
    [properties] Properties
      [_] commutative
-/
#guard_msgs in
example (a b c d e p q : Int) :
    a ∘ b = c ∘ d →
    a ∘ q = p →
    (c ∘ d) ∘ e = a ∘ (p ∘ q) := by
  grind only

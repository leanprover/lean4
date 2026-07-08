open Lean Grind AC
example {α : Type u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b c) = op (op a b) c := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b c) = op (op a b) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.LawfulIdentity op u] (a b c : α)
    : op a (op b c) = op (op a b) (op c u) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c : α)
    : op c (op b a) = op (op b a) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.LawfulIdentity op u] (a b c : α)
    : op a (op b c) = op (op b a) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.LawfulIdentity op u] (a b c : α)
    : op a (op b (op u c)) = op (op b a) (op u c) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c : α)
    : op (op a a) (op b c) = op (op a (op b b)) c := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op b b)) c := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] [Std.LawfulIdentity op u] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op (op u b) b)) c := by
  grind only

example {α : Type u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op b b)) c := by
  grind only

example {α : Type u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] [Std.LawfulIdentity op u] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op (op u b) b)) c := by
  grind only

example {α} (as bs cs : List α) : as ++ (bs ++ cs) = ((as ++ []) ++ bs) ++ (cs ++ []) := by
  grind only

example (a b c : Nat) : max a (max b c) = max (max b 0) (max a c) := by
  grind only

example (a b c : Nat) : max a (max b c) = max (max b 0) (max a c) ∧ min a b = min b a := by
  grind (splits := 0) only

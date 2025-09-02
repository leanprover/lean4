example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b b) = c → op c c = op (op a b) (op b c) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b b) = c → op (op a b) (op b c) = op c c := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b b) = c → op (op c a) (op b b) = op c c := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
    : op a (op b b) = c → op c c = op (op c a) (op b b) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
    : op a (op b b) = op c d → op c (op d c) = op (op a b) (op b c) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
    : op a (op b b) = op c d → op (op a b) (op b c) = op (op c d) c := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
    : op a (op b b) = op c d → op c (op c (op d c)) = op (op c a) (op b (op b c)) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
    : op a (op b b) = op c d → op (op c a) (op b (op b c)) = op c (op c (op d c))  := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c d : α)
    : op a (op b b) = op d c → op c (op d c) = op (op b a) (op b c) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c d : α)
    : op a (op b b) = op d c → op (op b a) (op b c) = op c (op d c)  := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op]
    (one : α) [Std.LawfulIdentity op one] (a b c d : α)
    : op a (op (op b one) b) = op d c → op (op b a) (op (op b one) c) = op (op c one) (op d c)  := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b : α)
    : op a (op a b) = op a a →
      op a (op b b) = op b b →
      op b (op b b) = op b b  := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] (a b : α)
    : op a (op a b) = op a a →
      op a (op b b) = op b b →
      a = b := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op]
    [Std.IdempotentOp op]
    (a b c d : α)
    : op a (op b b) = op d c → op (op b a) (op b c) = op c (op d c)  := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op]
    [Std.IdempotentOp op] (a b c d e f x y w : α)
    : op d (op c x) = op a b →
      op e (op f (op y w)) = op a (op b c) →
      op x (op c d) = op e (op w (op y f)) := by
  grind only

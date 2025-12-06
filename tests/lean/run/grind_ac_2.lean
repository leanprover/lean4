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

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c d e f x y w : α)
    : op d (op x c) = op a b →
      op e (op f (op y w)) = op a (op b c) →
      op d (op x c) = op e (op f (op y w)) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c d e f x y w : α)
    : op a (op d x) = op b c →
      op e (op f (op y w)) = op a (op b c) →
      op a (op d x) = op e (op f (op y w)) := by
  grind only

example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c d e f x y w : α)
    : op d (op x c) = op a b →
      op e (op f (op y w)) = op (op d a) (op b c) →
      op d (op x c) = op e (op f (op y w)) := by
  grind only

example {α β : Sort u} (f : α → β) (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b c d : α)
    : op a (op b b) = op d c → f (op (op b a) (op b c)) = f (op c (op d c)) := by
  grind only

example {α β : Sort u} (f : α → β) (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b : α)
    : f (op a b) = f (op b a) := by
  grind only

example {α : Sort u} (f : α → α) (op : α → α → α) [Std.Associative op] [Std.Commutative op] (a b : α)
    : op (f (op a b)) b = op b (f (op b a)) := by
  grind only

example {α β : Sort u} (bar : α → β) (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c d e f x y w : α)
    : op d (op x c) = op a b →
      op e (op f (op y w)) = op (op d a) (op b c) →
      bar (op d (op x c)) = bar (op e (op f (op y w))) := by
  grind only

example (a b c : Nat) : min a (max b c) = min (max c b) a := by
  grind -lia only

example (a b c : Nat) : min a (max b (max c 0)) = min (max c b) a := by
  grind -lia only

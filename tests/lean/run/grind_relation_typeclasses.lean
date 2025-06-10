set_option grind.warning false

example [Mul α] [Std.Commutative (α := α) (· * ·)] {a b : α} : a * b = b * a := by
  grind

example [Mul α] [Std.Associative (α := α) (· * ·)] {a b : α} : a * b * c = a * (b * c) := by
  grind

example [Mul α] [Std.Commutative (α := α) (· * ·)] [Std.Associative (α := α) (· * ·)] {a b c : α} :
    a * b * c = b * (a * c) := by
  grind

example [Mul α] [Std.IdempotentOp (α := α) (· * ·)] {a : α} : a * a = a := by
  grind

example [Mul α] [Std.IdempotentOp (α := α) (· * ·)] [Std.Commutative (α := α) (· * ·)]
    [Std.Associative (α := α) (· * ·)] {a : α} :
    a * b * a = a * b := by
  grind

example [Mul α] (a b : α) [Std.LawfulLeftIdentity (α := α) (· * ·) (a : α)] : a * b = b := by
  grind

example [Mul α] (a b : α) [Std.LawfulRightIdentity (α := α) (· * ·) (a : α)] : b * a = b := by
  grind

example [Mul α] (a b : α) [Std.LawfulRightIdentity (α := α) (· * ·) (a : α)] : b * a * a = b := by
  grind

example [Mul α] (a b : α) [Std.LawfulIdentity (α := α) (· * ·) (a : α)]
    [Std.Associative (α := α) (· * ·)] : a * b * a = b := by
  grind

example [Mul α] (a b : α) [Std.Commutative (α := α) (· * ·)] [Std.LawfulCommIdentity (α := α) (· * ·) (a : α)]
    [Std.Associative (α := α) (· * ·)] : a * b * a = b := by
  grind

example {r : α → α → Prop} [Std.Refl r] {a : α} : r a a := by grind

example [Mul α] {r : α → α → Prop} [Std.Commutative (α := α) (· * ·)] [Std.Refl r] :
    r (a * b) (b * a) := by grind

example {r : α → α → Prop} [Std.Antisymm r] {a b : α} : r a b → r b a → a = b := by grind
example {r : α → α → Prop} [Std.Asymm r] {a b : α} : r a b → r b a → False := by grind
example {r : α → α → Prop} [Std.Asymm r] {a b : α} : r a b → ¬ r b a := by grind
example {r : α → α → Prop} [Std.Asymm r] : Std.Antisymm r := by grind [Std.Antisymm] -- We haven't put `@[grind]` on `Std.Antisymm.mk`.
example {r : α → α → Prop} [Std.Total r] {a b : α} : ¬ r a b → r b a := by grind
example {r : α → α → Prop} [Std.Irrefl r] {a : α} : ¬ r a a := by grind
example [Mul α] {r : α → α → Prop} [Std.Commutative (α := α) (· * ·)] [Std.Irrefl r] :
    ¬ r (a * b) (b * a) := by
  grind
example [Mul α] {r : α → α → Prop} [Std.Commutative (α := α) (· * ·)] [Std.Total r]
    (h : ¬ r (a * b) (b * a)) : False := by
  grind

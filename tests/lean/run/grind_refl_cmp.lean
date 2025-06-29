import Std

example (f : α → α → Ordering) [Std.ReflCmp f] (a : α) : f a a = .eq := by
  grind

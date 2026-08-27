module
import Std.Data

example (f : α → α → Ordering) [Std.ReflCmp f] (a : α) : f a a = .eq := by
  grind

example (f : α → α → Ordering) [Std.ReflCmp f] (a b : α) (h : a = b) : f a b = .eq := by
  grind

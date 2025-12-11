module
import Std

example (f : α → α → Ordering) [Std.LawfulEqCmp f] (a b c : α) : b = c → f a b = o → o = .eq → a = c := by
  grind

example (a b c : Vector (List Nat) 10) : b = c → a.compareLex (List.compareLex compare) b = o → o = .eq → a = c := by
  grind

example (a b c : Vector (List Nat) 10) : b = c → o = .eq → a.compareLex (List.compareLex compare) b = o → a = c := by
  grind

example (a b c : Array (Vector (List Nat) n)) : b = c → o = .eq → a.compareLex (Vector.compareLex (List.compareLex compare)) b = o → a = c := by
  grind

example [Ord α] [Std.LawfulEqCmp (compare : α → α → Ordering)] (a b c : Array (Vector (List α) n))
    : b = c → o = .eq → a.compareLex (Vector.compareLex (List.compareLex compare)) b = o → a = c := by
  grind

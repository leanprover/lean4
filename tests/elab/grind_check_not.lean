module
import Std

theorem take_add' {l : List α} {i j : Nat} : l.take (i + j) = l.take i ++ (l.drop i).take j :=
  List.take_add

grind_pattern take_add' => (l.drop i).take j where
  check l ≠ []

attribute [-grind] List.take_add

example (l : List Nat) (n : Nat) : l.take (n + 1) = l.take n ++ (l.drop n).take 1 := by
  grind

example (l : List Nat) (a b : Nat) (h : a + b ≤ l.length) :
    (l.take (a + b)).count 0 = (l.take a).count 0 + ((l.drop a).take b).count 0 := by
  grind

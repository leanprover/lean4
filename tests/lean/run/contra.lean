theorem ex1 (p : Prop) (h1 : p) (h2 : p → False) : α := by
  contradiction

theorem ex2 (p : Prop) (h1 : p) (h2 : ¬ p) : α := by
  contradiction

theorem ex3 (p : Prop) (h1 : id p) (h2 : ¬ p) : α := by
  contradiction

theorem ex4 (p : Prop) (h1 : id p) (h2 : id (Not p)) : α := by
  contradiction

theorem ex5 (h : x+1 = 0) : α := by
  contradiction

theorem ex6 (h : 0+0 ≠ 0) : α := by
  contradiction

theorem ex7 (x : α) (h : Not (x = x)) : α := by
  contradiction

theorem ex8 (h : 0+0 = 0 → False) : α := by
  contradiction

theorem ex9 (h : 10 = 20) : α := by
  contradiction

theorem ex10 (h : [] = [1, 2, 3]) : α := by
  contradiction

theorem ex11 (h : id [] = [1, 2, 3]) : α := by
  contradiction

theorem ex12 (h : False) : α := by
  contradiction

theorem ex13 (h : id False) : α := by
  contradiction

theorem ex14 (h : 100000000 ≤ 20) : α := by
  contradiction

theorem ex15 (x : α) (h : x = x → False) : α := by
  contradiction

theorem ex16 (xs : List α) (h : xs = [] → False) : Nonempty α := by
  cases xs using List.rec with
  | nil      => contradiction
  | cons x _ => apply Nonempty.intro; assumption

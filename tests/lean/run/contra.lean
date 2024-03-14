def ex1 (p : Prop) (h1 : p) (h2 : p → False) : α := by
  contradiction

def ex2 (p : Prop) (h1 : p) (h2 : ¬ p) : α := by
  contradiction

def ex3 (p : Prop) (h1 : id p) (h2 : ¬ p) : α := by
  contradiction

def ex4 (p : Prop) (h1 : id p) (h2 : id (Not p)) : α := by
  contradiction

def ex5 (h : x+1 = 0) : α := by
  contradiction

def ex6 (h : 0+0 ≠ 0) : α := by
  contradiction

def ex7 (x : α) (h : Not (x = x)) : α := by
  contradiction

def ex8 (h : 0+0 = 0 → False) : α := by
  contradiction

def ex9 (h : 10 = 20) : α := by
  contradiction

def ex10 (h : [] = [1, 2, 3]) : α := by
  contradiction

def ex11 (h : id [] = [1, 2, 3]) : α := by
  contradiction

def ex12 (h : False) : α := by
  contradiction

def ex13 (h : id False) : α := by
  contradiction

def ex14 (h : 100000000 ≤ 20) : α := by
  contradiction

def ex15 (x : α) (h : x = x → False) : α := by
  contradiction

theorem ex16 (xs : List α) (h : xs = [] → False) : Nonempty α := by
  cases xs using List.rec with
  | nil      => contradiction
  | cons x _ => apply Nonempty.intro; assumption

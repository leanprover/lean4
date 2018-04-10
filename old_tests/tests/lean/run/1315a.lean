def k : ℕ := 0

def works : Π (n : ℕ) (m : ℕ), ℕ
| 0 m := 0
| (n+1) m :=
  let val := m+1 in
  match works n val with
  | 0 := 0
  | (l+1) := 0
  end

def works2 : Π (n : ℕ) (m : ℕ), ℕ
| 0 m := 0
| (n+1) m :=
  match k with
  | 0 := 0
  | (i+1) :=
  match works2 n (m+1) with
  | 0 := 0
  | (l+1) := 0
  end
 end

def fails : Π (n : ℕ) (m : ℕ), ℕ
| 0 m := 0
| (n+1) m :=
  match k with
  | 0 := 0
  | (i+1) :=
  let val := m+1 in
  match fails n val with
  | 0 := 0
  | (l+1) := 0
  end
 end

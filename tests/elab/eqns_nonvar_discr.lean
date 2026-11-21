/-!
Equation lemmas of a definition by `match` where a discriminant is not a variable and another one
is. Splitting the `match` produces a hypothesis `discr = pattern` or `discr ≍ pattern` for the
former. It is unified:
a contradictory one closes the case, and the other ones instantiate the pattern variables.
-/

/-! A literal discriminant that is different from a literal pattern: the alternative is unreachable. -/

def strLit (s : String) : Nat :=
  match "b", s with
  | "a", _ => 1
  | "b", "c" => 2
  | _, _ => 3

/--
info: equations:
theorem strLit.eq_1 : strLit "c" = 2
theorem strLit.eq_2 : ∀ (s_1 : String), ("b" = "b" → s_1 = "c" → False) → strLit s_1 = 3
-/
#guard_msgs in
#print equations strLit

def charLit (s : String) : Nat :=
  match 'b', s with
  | 'a', _ => 1
  | 'b', "c" => 2
  | _, _ => 3

/--
info: equations:
theorem charLit.eq_1 : charLit "c" = 2
theorem charLit.eq_2 : ∀ (s_1 : String), ('b' = 'b' → s_1 = "c" → False) → charLit s_1 = 3
-/
#guard_msgs in
#print equations charLit

def natLit (s : String) : Nat :=
  match 1, s with
  | 0, _ => 1
  | 1, "c" => 2
  | _, _ => 3

/--
info: equations:
theorem natLit.eq_1 : natLit "c" = 2
theorem natLit.eq_2 : ∀ (s_1 : String), (1 = 1 → s_1 = "c" → False) → natLit s_1 = 3
-/
#guard_msgs in
#print equations natLit

/-! A discriminant that is a constructor application: the pattern variables are instantiated. -/

def succDiscr (s : String) (n : Nat) : Nat :=
  match n + 1, s with
  | 0, _ => 1
  | k + 1, "c" => k
  | _, _ => 3

/--
info: equations:
theorem succDiscr.eq_1 : ∀ (n : Nat) (s_1 : String), n + 1 = 0 → succDiscr s_1 n = 1
theorem succDiscr.eq_2 : ∀ (n : Nat), succDiscr "c" n = n
theorem succDiscr.eq_3 : ∀ (n : Nat) (s_1 : String),
  (n + 1 = 0 → False) → (∀ (k : Nat), n + 1 = k.succ → s_1 = "c" → False) → succDiscr s_1 n = 3
-/
#guard_msgs in
#print equations succDiscr

def someDiscr (s : String) (n : Nat) : Nat :=
  match some n, s with
  | none, _ => 1
  | some k, "c" => k
  | _, _ => 3

/--
info: equations:
theorem someDiscr.eq_1 : ∀ (n : Nat), someDiscr "c" n = n
theorem someDiscr.eq_2 : ∀ (n : Nat) (s_1 : String),
  (some n = none → False) → (∀ (k : Nat), some n = some k → s_1 = "c" → False) → someDiscr s_1 n = 3
-/
#guard_msgs in
#print equations someDiscr

def pairDiscr (s : String) (n m : Nat) : Nat :=
  match (n, m + 1), s with
  | (a, b + 1), "c" => a + b
  | (a, _), _ => a

/--
info: equations:
theorem pairDiscr.eq_1 : ∀ (n m : Nat), pairDiscr "c" n m = n + m
theorem pairDiscr.eq_2 : ∀ (n m : Nat) (s_1 : String),
  (∀ (b : Nat), s_1 = "c" → m + 1 = b.succ → False) → pairDiscr s_1 n m = n
-/
#guard_msgs in
#print equations pairDiscr

/-! The same discriminants bound by `have` and `let`. -/

def haveLit (s : String) : Nat :=
  have t := "b"
  match t, s with
  | "a", _ => 1
  | "b", "c" => 2
  | _, _ => 3

/--
info: equations:
theorem haveLit.eq_1 : haveLit "c" = 2
theorem haveLit.eq_2 : ∀ (s_1 : String), ("b" = "b" → s_1 = "c" → False) → haveLit s_1 = 3
-/
#guard_msgs in
#print equations haveLit

def letSucc (s : String) (n : Nat) : Nat :=
  let m := n + 1
  match m, s with
  | 0, _ => 1
  | k + 1, "c" => k
  | _, _ => 3

/--
info: equations:
theorem letSucc.eq_1 : ∀ (n : Nat) (s_1 : String), n + 1 = 0 → letSucc s_1 n = 1
theorem letSucc.eq_2 : ∀ (n : Nat), letSucc "c" n = n
theorem letSucc.eq_3 : ∀ (n : Nat) (s_1 : String),
  (n + 1 = 0 → False) → (∀ (k : Nat), n + 1 = k.succ → s_1 = "c" → False) → letSucc s_1 n = 3
-/
#guard_msgs in
#print equations letSucc

/-!
Dependent discriminants: the hypothesis for the second discriminant is a heterogeneous equality,
and it is unified after the one for the first discriminant.
-/

inductive Vec : Nat → Type where
  | nil : Vec 0
  | cons : Nat → Vec n → Vec (n+1)

def depVar (n : Nat) (v : Vec (n+1)) (s : String) : Nat :=
  match n + 1, v, s with
  | _, .cons a _, "c" => a
  | _, _, _ => 0

/--
info: equations:
theorem depVar.eq_1 : ∀ (n a : Nat) (a_1 : Vec n), depVar n (Vec.cons a a_1) "c" = a
theorem depVar.eq_2 : ∀ (n : Nat) (s_1 : String) (v_1 : Vec (n + 1)),
  (∀ (n_1 a : Nat) (a_1 : Vec n_1), n + 1 = n_1 + 1 → v_1 ≍ Vec.cons a a_1 → s_1 = "c" → False) → depVar n v_1 s_1 = 0
-/
#guard_msgs in
#print equations depVar

def depCtor (n : Nat) (w : Vec n) (s : String) : Nat :=
  match n + 1, Vec.cons 5 w, s with
  | _, .cons a _, "c" => a
  | _, _, _ => 0

/--
info: equations:
theorem depCtor.eq_1 : ∀ (n : Nat) (w : Vec n), depCtor n w "c" = 5
theorem depCtor.eq_2 : ∀ (n : Nat) (w : Vec n) (s_1 : String),
  (∀ (n_1 a : Nat) (a_1 : Vec n_1), n + 1 = n_1 + 1 → Vec.cons 5 w ≍ Vec.cons a a_1 → s_1 = "c" → False) →
    depCtor n w s_1 = 0
-/
#guard_msgs in
#print equations depCtor

def depSucc (n : Nat) (w : Vec n) (s : String) : Nat :=
  match n + 1, Vec.cons 5 w, s with
  | 0, _, _ => 1
  | k + 1, .cons a _, "c" => a + k
  | _, _, _ => 0

/--
info: equations:
theorem depSucc.eq_1 : ∀ (n : Nat) (w : Vec n) (s_1 : String), n + 1 = 0 → depSucc n w s_1 = 1
theorem depSucc.eq_2 : ∀ (n : Nat) (w : Vec n), depSucc n w "c" = 5 + n
theorem depSucc.eq_3 : ∀ (n : Nat) (w : Vec n) (s_1 : String),
  (∀ (x : Vec 0), n + 1 = 0 → Vec.cons 5 w ≍ x → False) →
    (∀ (k a : Nat) (a_1 : Vec k), n + 1 = k.succ → Vec.cons 5 w ≍ Vec.cons a a_1 → s_1 = "c" → False) →
      depSucc n w s_1 = 0
-/
#guard_msgs in
#print equations depSucc

/-! A recursive definition. -/

def recSome : Nat → String → Nat
  | 0, _ => 0
  | n + 1, s =>
    match some n, s with
    | some k, "c" => recSome n s + k
    | _, _ => 0

/--
info: equations:
@[backward_defeq] theorem recSome.eq_1 : ∀ (x : String), recSome 0 x = 0
theorem recSome.eq_2 : ∀ (n : Nat), recSome n.succ "c" = recSome n "c" + n
theorem recSome.eq_3 : ∀ (n : Nat) (s : String), (∀ (k : Nat), some n = some k → s = "c" → False) → recSome n.succ s = 0
-/
#guard_msgs in
#print equations recSome

def diag : Bool → Bool → Bool → Nat
| b,  true, false => 1
| false, b,  true => 2
| true, false, b  => 3
| b1, b2, b3 => arbitrary

theorem diag1 (a : Bool) : diag a true false = 1 :=
match a with
| true  => rfl
| false => rfl

theorem diag2 (a : Bool) : diag false a true = 2 :=
by cases a; exact rfl; exact rfl

theorem diag3 (a : Bool) : diag true false a = 3 :=
by cases a; exact rfl; exact rfl

theorem diag4_1 : diag false false false = arbitrary :=
rfl

theorem diag4_2 : diag true true true = arbitrary :=
rfl

def f : Nat → Nat → Nat
| n, 0 => 0
| 0, n => 1
| n, m => arbitrary

theorem f_zero_right : (a : Nat) → f a 0 = 0
| 0   => rfl
| a+1 => rfl

theorem f_zero_succ (a : Nat) : f 0 (a+1) = 1 :=
rfl

theorem f_succ_succ (a b : Nat) : f (a+1) (b+1) = arbitrary :=
rfl

def app {α} : List α → List α → List α
| [],   l => l
| h::t, l => h :: (app t l)

theorem app_nil {α} (l : List α) : app [] l = l :=
rfl

theorem app_cons {α} (h : α) (t l : List α) : app (h :: t) l = h :: (app t l) :=
rfl

theorem ex : app [1, 2] [3,4,5] = [1,2,3,4,5] :=
rfl

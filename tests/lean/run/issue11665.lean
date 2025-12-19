opaque opq : Nat → Nat

/-- A particular tricky inductive type -/
inductive T : Nat → Type where
  | mk3 n : T (n + 1)
  | mk4 n : T (opq n) -- Removing this constructor makes the issue go away

def test1 : (n : Nat) → T n → Unit
   | Nat.succ _, T.mk3 _ => ()
   | _, _ => ()

def eqns := @test1.match_1.eq_1 -- used to fail
def congreqns := @test1.match_1.congr_eq_1 -- used to faile

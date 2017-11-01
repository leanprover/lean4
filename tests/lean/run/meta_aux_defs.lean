def f : nat → nat
| 0     := 1
| (n+1) := f n + 10

#print f._main._meta_aux

#print nat.add._main._meta_aux

-- set_option trace.debug.eqn_compiler.wf_rec true
mutual def even, odd
with even : nat → bool
| 0     := tt
| (n+1) := odd n
with odd : nat → bool
| 0     := ff
| (n+1) := even n

#print even._main

#print even._main._meta_aux
#print odd._main._meta_aux

def fib : nat → nat
| 0     := 1
| 1     := 1
| (n+2) := fib (n+1) + fib n

#eval fib 2

inductive stmt
| dec   : stmt
| while : stmt → stmt
| print : string → stmt
| seq   : stmt → stmt → stmt

def eval : nat → nat → string → stmt → option (nat × string)
| (f+1) v o (stmt.print s)   := some (v, o ++ s)
| (f+1) v o stmt.dec         := some (v - 1, o)
| (f+2) v o (stmt.seq s₁ s₂) :=
  match eval (f+1) v o s₁ with
  | some (v₁, o₁) := eval f v₁ o₁ s₂
  | none          := none
  end
| (f+2) v o (stmt.while s)   :=
  if v > 0 then
    match eval (f+1) v o s with
    | some (v₁, o₁) := eval f v₁ o₁ (stmt.while s)
    | none          := none
    end
  else
    some (v, o)
| _     v o s                := none

/- The performance of the following eval should not depend on the first argument. -/
#eval eval 1000000000 3 "" (stmt.while (stmt.seq stmt.dec (stmt.print "hello\n")))

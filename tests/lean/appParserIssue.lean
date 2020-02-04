def f (x : Nat) (g : Nat → Nat) := g x

new_frontend

#check f 1 fun x => x   -- should fail
#check f 1 (fun x => x) -- should work
#check f 1 $ fun x => x -- should work

syntax "foo" term:max term:max : term
macro_rules `(foo $x $y) => `(f $x $y)

#check foo 1 fun x => x   -- should fail?
#check foo 1 (fun x => x) -- should work


def f (x : Nat) (g : Nat → Nat) := g x

#check f 1 fun x => x   -- should work
#check f 1 (fun x => x) -- should work
#check f 1 $ fun x => x -- should work

syntax "foo" term:max term:max : term
macro_rules | `(foo $x $y) => `(f $x $y)

#check foo 1 (fun x => x) -- should work
#check foo 1 fun x => x   -- should work

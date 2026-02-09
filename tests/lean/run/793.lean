macro "foo" x:ident : command =>
  `(structure Foo where
      val : Nat
      prop : val = 42
    def f (x : Foo) := x.val
    def g : Foo := { val := 42, prop := by decide }
    theorem $x:ident (x : Foo) : f x = 42 := by simp [f, x.prop] )

foo test

/--
info: theorem test : ∀ (x : Foo✝), f✝ x = 42 :=
fun x => of_eq_true (Eq.trans (congrFun' (congrArg Eq (Foo.prop✝ x)) 42) (eq_self 42))
-/
#guard_msgs in
#print test

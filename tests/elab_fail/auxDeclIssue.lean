--

theorem ex1 : False :=
by {
   assumption -- should not use the auxiliary declaration `ex1 : False`
}

variable (x y : Nat) in
theorem ex2 : x = y :=
by {
  subst x; -- should not use the auxiliary declaration `ex2 : x = y`
  exact rfl
}

set_option pp.auxDecls true in
theorem ex3 : False :=
by {
   assumption -- should not use the auxiliary declaration `ex1 : False`
}

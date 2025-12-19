inductive L (α : Type u) : Type u where
  | nil : L α
  | cons (x : α) (xs : L α) : L α

-- Check that L.cons.inj uses the per-ctor noConfusion principle
/--
info: theorem L.cons.inj.{u} : ∀ {α : Type u} {x : α} {xs : L α} {x_1 : α} {xs_1 : L α},
  L.cons x xs = L.cons x_1 xs_1 → x = x_1 ∧ xs = xs_1 :=
fun {α} {x} {xs} {x_1} {xs_1} x_2 => L.cons.noConfusion x_2 fun x_eq xs_eq => ⟨eq_of_heq x_eq, eq_of_heq xs_eq⟩
-/
#guard_msgs in
#print L.cons.inj

-- Check that injection uses the per-ctor noConfusion principle

theorem ex1 (h : L.cons x xs = L.cons y ys) : x = y ∧ xs = ys := by
  injection h
  repeat constructor <;> assumption

/--
info: theorem ex1.{u_1} : ∀ {α : Type u_1} {x : α} {xs : L α} {y : α} {ys : L α},
  L.cons x xs = L.cons y ys → x = y ∧ xs = ys :=
fun {α} {x} {xs} {y} {ys} h => L.cons.noConfusion h fun x_eq xs_eq => ⟨eq_of_heq x_eq, eq_of_heq xs_eq⟩
-/
#guard_msgs in #print ex1

-- Check that injection does not intro more than it should
theorem ex2 (h : L.cons x xs = L.cons y ys) : Unit → x = y ∧ xs = ys := by
  injection h
  intro u
  repeat constructor <;> assumption

-- Check that grind uses `L.cons.noConfusion`

theorem ex3 (h : L.cons x xs = L.cons y ys) : x = y ∧ xs = ys := by
  grind
/--
info: theorem ex3._proof_1_1.{u_1} : ∀ {α : Type u_1} {x : α} {xs : L α} {y : α} {ys : L α},
  L.cons x xs = L.cons y ys → x = y ∧ xs = ys :=
fun {α} {x} {xs} {y} {ys} h =>
  Classical.byContradiction
    (Lean.Grind.intro_with_eq (¬(x = y ∧ xs = ys)) (¬x = y ∨ ¬xs = ys) False (Lean.Grind.not_and (x = y) (xs = ys))
      fun h_1 =>
      id
        (Eq.mp
          (Eq.trans (Eq.symm (eq_true (L.cons.inj (id h)).1))
            (Lean.Grind.eq_false_of_not_eq_true
              (Eq.trans
                (Eq.symm
                  (Lean.Grind.or_eq_of_eq_false_right (Lean.Grind.not_eq_of_eq_true (eq_true (L.cons.inj (id h)).2))))
                (eq_true h_1))))
          True.intro))
-/
#guard_msgs in #print ex3._proof_1_1


-- Check that for numary constructors, we get a trivial inlined “no confusion” principle

inductive AlmostEnum where | a | b | mk (b : Bool)

-- No explicit noConfusion principle for `AlmostEnum.a`:
/-- error: Unknown constant `AlmostEnum.a.noConfusion` -/
#guard_msgs in #print sig AlmostEnum.a.noConfusion


set_option linter.unusedVariables false in
theorem ex4 (h : AlmostEnum.a = AlmostEnum.a) : True := by
  injection h
  trivial

/--
info: theorem ex4 : AlmostEnum.a = AlmostEnum.a → True :=
fun h => (fun P => P) True.intro
-/
#guard_msgs in #print ex4

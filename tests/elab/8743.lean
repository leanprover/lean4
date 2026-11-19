/-!
# Generalized field notation allows explicit universes

https://github.com/leanprover/lean4/issues/8743
-/

set_option warn.sorry false
set_option pp.universes true
set_option pp.mvars.anonymous false

/-!
Kenny Lau's example. This used to give "invalid use of explicit universe parameters, 'x' is a local variable"
since generalized field notation was improperly attributing the explicit universe to `x` itself, not the projection.
-/
section
def Foo : Type u := sorry
def Foo.inv.{v,u} : Foo.{u} → Foo.{v} := sorry

variable (x : Foo.{u})
/-- info: Foo.inv.{2, u} x : Foo.{2} -/
#guard_msgs in #check Foo.inv.{2} x
/-- info: Foo.inv.{2, u} x : Foo.{2} -/
#guard_msgs in #check x.inv.{2}
/-- info: Foo.inv.{u, u} x : Foo.{u} -/
#guard_msgs in #check x.inv.{u}
/-- info: Foo.inv.{2, u} x : Foo.{2} -/
#guard_msgs in #check Foo.inv.{2,u} x
/-- info: Foo.inv.{2, u} x : Foo.{2} -/
#guard_msgs in #check x.inv.{2,u}
/--
error: Application type mismatch: The argument
  x
has type
  Foo.{u}
of sort `Type u` but is expected to have type
  Foo.{2}
of sort `Type 2` in the application
  Foo.inv.{u, 2} x
---
info: Foo.inv.{u, 2} sorry : Foo.{u}
-/
#guard_msgs in #check x.inv.{u,2}

/-!
That example was an explicit universe applied to the identifier syntax `x.inv`.
New feature: it's possible to apply dot notation to expressions too:
-/
/-- info: Foo.inv.{u, u} x : Foo.{u} -/
#guard_msgs in #check (x).inv.{u}
/-- info: Foo.inv.{2, u} x : Foo.{2} -/
#guard_msgs in #check (x).inv.{2}

/-!
New feature: it's possible to chain field notations.
-/
/-- info: Foo.inv.{4, 3} (Foo.inv.{3, u} x) : Foo.{4} -/
#guard_msgs in #check Foo.inv.{4} (Foo.inv.{3} x)
/-- info: Foo.inv.{4, 3} (Foo.inv.{3, u} x) : Foo.{4} -/
#guard_msgs in #check x.inv.{3}.inv.{4}
/-- info: Foo.inv.{4, u_1} (Foo.inv.{u_1, u} x) : Foo.{4} -/
#guard_msgs in #check x.inv.inv.{4}
/-- info: Foo.inv.{u_1, 3} (Foo.inv.{3, u} x) : Foo.{u_1} -/
#guard_msgs in #check x.inv.{3}.inv
/-- info: Foo.inv.{4, 3} (Foo.inv.{3, u} x) : Foo.{4} -/
#guard_msgs in #check (x).inv.{3}.inv.{4}
/-- info: Foo.inv.{4, u_1} (Foo.inv.{u_1, u} x) : Foo.{4} -/
#guard_msgs in #check (x).inv.inv.{4}
/-- info: Foo.inv.{u_1, 3} (Foo.inv.{3, u} x) : Foo.{u_1} -/
#guard_msgs in #check (x).inv.{3}.inv

end


/-!
Eric Wieser's example from the issue.
-/
abbrev Nat.ulift.{u} (n : Nat) : ULift.{u} Nat := ULift.up.{u} n

/-- info: Nat.ulift.{5} 1 : ULift.{5, 0} Nat -/
#guard_msgs in #check Nat.ulift.{5} (1 : Nat)
/-- info: Nat.ulift.{5} 1 : ULift.{5, 0} Nat -/
#guard_msgs in #check (1 : Nat).ulift.{5}


/-!
Mario Carneiro's example from the issue
-/
/-- info: Nat.ulift.{5} 1 : ULift.{5, 0} Nat -/
#guard_msgs in #check (1 : Nat) |>.ulift.{5}
/-- info: Nat.ulift.{u_1} 1 : ULift.{u_1, 0} Nat -/
#guard_msgs in #check (1 : Nat) |>.ulift

/-!
Check that `|>.` notation supports arguments, with and without universes.
-/
section
def Foo.add.{u} : Foo.{u} → Nat → Foo.{u} := sorry

variable (x : Foo.{3})
/-- info: Foo.add.{3} x 2 : Foo.{3} -/
#guard_msgs in #check x |>.add.{3} 2
/-- info: Foo.add.{3} x 2 : Foo.{3} -/
#guard_msgs in #check x |>.add 2
/--
error: Application type mismatch: The argument
  x
has type
  Foo.{3}
of sort `Type 3` but is expected to have type
  Foo.{4}
of sort `Type 4` in the application
  Foo.add.{4} x
---
info: Foo.add.{4} sorry 2 : Foo.{4}
-/
#guard_msgs in #check x |>.add.{4} 2
/-- info: Foo.add.{3} x : Nat → Foo.{3} -/
#guard_msgs in #check x |>.add
/-- info: Foo.add.{3} x : Nat → Foo.{3} -/
#guard_msgs in #check x |>.add.{3}
/-- info: Foo.add.{3} (Foo.add.{3} x 2) : Nat → Foo.{3} -/
#guard_msgs in #check x |>.add.{3} 2 |>.add.{3}

end

/-!
Named structure projections allow explicit universes.
These have a different code path from generalized field notation.
-/
/-- info: fun p => Prod.fst.{u_1, u_2} p : Prod.{u_1, u_2} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p.fst
/-- info: fun p => Prod.fst.{u_1, u_2} p : Prod.{u_1, u_2} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p |>.fst
/-- info: fun p => Prod.fst.{1, u_1} p : Prod.{1, u_1} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p.fst.{1}
/-- info: fun p => Prod.fst.{1, u_1} p : Prod.{1, u_1} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p |>.fst.{1}
/-- info: fun p => Prod.fst.{1, 2} p : Prod.{1, 2} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p.fst.{1,2}
/-- info: fun p => Prod.fst.{1, 2} p : Prod.{1, 2} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p |>.fst.{1,2}

/-!
Indexed projections allow explicit universes for `structure`s.
-/
/-- info: fun p => Prod.fst.{1, u_1} p : Prod.{1, u_1} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p.1.{1}
/-- info: fun p => Prod.fst.{1, u_1} p : Prod.{1, u_1} ?_ ?_ → ?_ -/
#guard_msgs in #check fun (p : _ × _) => p |>.1.{1}

/-!
Indexed projections don't allow explicit universes for structures not defined using `inductive`.
-/
inductive IPair (α : Type u) where
  | mk (x y : α)
/-- info: fun p => p.1 : IPair.{u_1} ?_ → ?_ -/
#guard_msgs in #check fun (p : IPair _) => p.1
/--
error: Invalid projection: Explicit universe levels are only supported for inductive types defined using the `structure` command. The expression
  p
has type `IPair.{_} ?_` which is not a `structure`.
---
info: fun p => sorry : (p : IPair.{u_1} ?_) → ?_ p
-/
#guard_msgs in #check fun (p : IPair _) => p.1.{0}

/-!
Inherited structure projections can be counterintuitive, since the universe levels apply to the
projection function *after* the base projection.
-/
section
structure S1 (α : Type u) where
  x : α
structure S2.{v,u} (α : Type u) (β : Type v) extends S1 α

variable (s : S2.{5,6} PUnit PUnit)
/-- info: S1.x.{6} (S2.toS1.{5, 6} s) : PUnit.{7} -/
#guard_msgs in #check s.x
-- Surprisingly, even though it's `S2.{5,6}`, `s.x.{5}` doesn't work ...
/--
error: Application type mismatch: The argument
  S2.toS1.{5, 6} s
has type
  S1.{6} PUnit.{7}
of sort `Type 6` but is expected to have type
  S1.{5} ?_
of sort `Type 5` in the application
  S1.x.{5} (S2.toS1.{5, 6} s)
-/
#guard_msgs in #check s.x.{5}
-- ... but `s.x.{6}` does
/-- info: S1.x.{6} (S2.toS1.{5, 6} s) : PUnit.{7} -/
#guard_msgs in #check s.x.{6}

end

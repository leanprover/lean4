import Std.Do

/-
Section variables should not be included.
-/
variable {Q : Std.Do.PostCond α ps}
def Id.instLawfulMonad' : LawfulMonad Id := by
  apply LawfulMonad.mk' <;> (simp only [Functor.map, id, Functor.mapConst, Seq.seq, SeqRight.seqRight, SeqLeft.seqLeft, bind, pure]; grind)

/-- info: Id.instLawfulMonad'.{u_1} : LawfulMonad Id -/
#guard_msgs in
#check Id.instLawfulMonad'

/-
Note that they are included when using `grind +revert`.
The problem is that the idiom `revert` and then re-`intro` while simplifying creates the
illusion that the section variables are needed.
-/
def Id.instLawfulMonad'' : LawfulMonad Id := by
  apply LawfulMonad.mk' <;> (simp only [Functor.map, id, Functor.mapConst, Seq.seq, SeqRight.seqRight, SeqLeft.seqLeft, bind, pure]; grind +revert)

/--
info: Id.instLawfulMonad''.{u_1, u_2} {α : Type u_2} {ps : Std.Do.PostShape} {Q : Std.Do.PostCond α ps} : LawfulMonad Id
-/
#guard_msgs in
#check Id.instLawfulMonad''

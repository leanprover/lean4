/-!
# `mutual_multiuniverse`

A mutual inductive block whose members live at three different universes:
`Prop`, `Type 0` and `Type 2`.  The kernel cannot accept such a block directly,
so the command lowers it; what the user sees is the block they asked for.
-/

mutual_multiuniverse
inductive A : Prop where
  | fromB : B → A
  | fromC : C → A
inductive B : Type 0 where
  | fromA : Nat → A → B
  | wrap : B → B
inductive C : Type 2 where
  | fromA : A → C
  | higherUniv : Nat → Type → C
  | pair : B → C → C
end

/-! The block-wide recursor has one motive per member, each at that member's
own universe, and every member's is at the same telescope: that uniformity is
what lets one member's recursor supply the induction hypothesis for a field of
another member's type. -/

/--
info: @A.mutualRec : ∀ {motive_1 : A → Prop} {motive_2 : B → Sort u_1} {motive_3 : C → Sort u_2},
  (∀ (a : B) (ih_1 : motive_2 a), motive_1 (A.fromB a)) →
    (∀ (a : C) (ih_1 : motive_3 a), motive_1 (A.fromC a)) →
      ∀ (case_3 : (a : Nat) → (a_1 : A) → motive_1 a_1 → motive_2 (B.fromA a a_1))
        (case_4 : (a : B) → motive_2 a → motive_2 a.wrap) (case_5 : (a : A) → motive_1 a → motive_3 (C.fromA a))
        (case_6 : (a : Nat) → (a_1 : Type) → motive_3 (C.higherUniv a a_1))
        (case_7 : (a : B) → (a_1 : C) → motive_2 a → motive_3 a_1 → motive_3 (C.pair a a_1)) (t : A), motive_1 t
-/
#guard_msgs in
set_option pp.proofs true in
#check @A.mutualRec

/--
info: @C.mutualRec : {motive_1 : A → Prop} →
  {motive_2 : B → Sort u_1} →
    {motive_3 : C → Sort u_2} →
      (∀ (a : B) (ih_1 : motive_2 a), motive_1 (A.fromB a)) →
        (∀ (a : C) (ih_1 : motive_3 a), motive_1 (A.fromC a)) →
          ((a : Nat) → (a_1 : A) → motive_1 a_1 → motive_2 (B.fromA a a_1)) →
            ((a : B) → motive_2 a → motive_2 a.wrap) →
              ((a : A) → motive_1 a → motive_3 (C.fromA a)) →
                ((a : Nat) → (a_1 : Type) → motive_3 (C.higherUniv a a_1)) →
                  ((a : B) → (a_1 : C) → motive_2 a → motive_3 a_1 → motive_3 (C.pair a a_1)) → (t : C) → motive_3 t
-/
#guard_msgs in
set_option pp.proofs true in
#check @C.mutualRec

/-! The data members are declared as honest inductive types, so they also have
their own native recursors.  `B` and `C` end up in separate strongly connected
components of the data-only dependency graph (`C` mentions `B`, but not the
other way round), so `C.rec` has a single motive and gives no induction
hypothesis for `C.pair`'s `B` field.  `C.mutualRec` is the one that does. -/

/--
info: @C.rec : {motive : C → Sort u_1} →
  ((a : A) → motive (C.fromA a)) →
    ((a : Nat) → (a_1 : Type) → motive (C.higherUniv a a_1)) →
      ((a : B) → (a_1 : C) → motive a_1 → motive (C.pair a a_1)) → (t : C) → motive t
-/
#guard_msgs in
#check @C.rec

/-- info: 'A.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms A.mutualRec

/-- info: 'B.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms B.mutualRec

/-- info: 'C.mutualRec' does not depend on any axioms -/
#guard_msgs in
#print axioms C.mutualRec

/-- A `Prop` member has no native recursor to compete with, so it also answers
to `A.rec`. -/
example : @A.rec = @A.mutualRec := rfl

/-! Every iota rule holds by `rfl`, including the ones that cross between
universes. -/

section
variable {mA : A → Prop} {mB : B → Sort u} {mC : C → Sort v}
  (fAB : (b : B) → mB b → mA (A.fromB b))
  (fAC : (c : C) → mC c → mA (A.fromC c))
  (fBa : (n : Nat) → (a : A) → mA a → mB (B.fromA n a))
  (fBw : (b : B) → mB b → mB (B.wrap b))
  (fCa : (a : A) → mA a → mC (C.fromA a))
  (fCh : (n : Nat) → (t : Type) → mC (C.higherUniv n t))
  (fCp : (b : B) → (c : C) → mB b → mC c → mC (C.pair b c))

example (b : B) :
    @B.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp (B.wrap b)
      = fBw b (@B.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp b) := rfl

example (n : Nat) (a : A) :
    @B.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp (B.fromA n a)
      = fBa n a (@A.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp a) := rfl

example (a : A) :
    @C.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp (C.fromA a)
      = fCa a (@A.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp a) := rfl

example (n : Nat) (t : Type) :
    @C.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp (C.higherUniv n t) = fCh n t := rfl

example (b : B) (c : C) :
    @C.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp (C.pair b c)
      = fCp b c (@B.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp b)
               (@C.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp c) := rfl

-- the `Prop` member's iota rules hold by proof irrelevance
example (b : B) :
    @A.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp (A.fromB b)
      = fAB b (@B.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp b) := rfl

example (c : C) :
    @A.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp (A.fromC c)
      = fAC c (@C.mutualRec mA mB mC fAB fAC fBa fBw fCa fCh fCp c) := rfl
end

/-! The data members are honest inductive types, so `match`, structural
recursion, `induction`, `injection` and `#eval` all work on them natively and
the block's computational content is not stuck behind a recursor. -/

def sizeB : B → Nat
  | .fromA n _ => n
  | .wrap b => sizeB b + 1

def sizeC : C → Nat
  | .fromA _ => 0
  | .higherUniv n _ => n
  | .pair b c => sizeB b + sizeC c

/-- info: 7 -/
#guard_msgs in
#eval sizeB (B.wrap (B.wrap (B.fromA 5 (A.fromC (C.higherUniv 3 Nat)))))

/-- info: 15 -/
#guard_msgs in
#eval sizeC (C.pair (B.wrap (B.fromA 4 (A.fromC (C.higherUniv 1 Nat)))) (C.higherUniv 10 Nat))

example (b : B) : sizeB (B.wrap b) = sizeB b + 1 := rfl

example (b : B) : 0 < sizeB (B.wrap b) := by
  induction b with
  | fromA n a => simp [sizeB]
  | wrap b ih => simp [sizeB]

example (m n : Nat) (a a' : A) (h : B.fromA m a = B.fromA n a') : m = n := by
  injection h

example (n : Nat) (a : A) (b : B) : B.fromA n a ≠ B.wrap b := by
  intro h; cases h

/-! The block-wide recursor is what to use when the recursion genuinely crosses
members, and it is computable.  The code generator compiles no recursor
application -- `B.rec` no more than `Nat.rec` -- so `B.mutualRec` is given a
compiled companion that does the same recursion by cases, and definitions built
from it both reduce in the kernel and evaluate. -/

def depth : B → Nat :=
  @B.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ => 0) (fun _ ih => ih + 1)
    (fun _ _ => 0) (fun n _ => n) (fun _ _ ihb ihc => ihb + ihc)

def depthC : C → Nat :=
  @C.mutualRec (fun _ => True) (fun _ => Nat) (fun _ => Nat)
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ => 0) (fun _ ih => ih + 1)
    (fun _ _ => 0) (fun n _ => n) (fun _ _ ihb ihc => ihb + ihc)

example : depth (B.wrap (B.wrap (B.fromA 5 (A.fromC (C.higherUniv 3 Nat))))) = 2 := rfl

/-- info: 2 -/
#guard_msgs in
#eval depth (B.wrap (B.wrap (B.fromA 5 (A.fromC (C.higherUniv 3 Nat)))))

-- `C.pair` folds a `Type 0` value into a `Type 2` recursion, so this crosses
-- both the `Prop` member and the two data universes
example : depthC (C.pair (B.wrap (B.fromA 4 (A.fromC (C.higherUniv 1 Nat))))
    (C.higherUniv 10 Nat)) = 11 := rfl

/-- info: 11 -/
#guard_msgs in
#eval depthC (C.pair (B.wrap (B.fromA 4 (A.fromC (C.higherUniv 1 Nat)))) (C.higherUniv 10 Nat))

-- the companion is compiler-only, so it changes nothing about the term
/-- info: 'depth' does not depend on any axioms -/
#guard_msgs in
#print axioms depth

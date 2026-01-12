import Lean
/-!
## Checking that let-to-have is applied to definitions and equation lemmas
-/

set_option pp.letVarTypes true
set_option pp.mvars.anonymous false

/-!
Non-recursive definitions have the transformation applied on the declaration itself.
-/

def fnNonRec (n : Nat) : let α := Nat; α :=
  let m := n + 1
  m
/--
info: def fnNonRec : Nat →
  have α : Type := Nat;
  α :=
fun n =>
  have m : Nat := n + 1;
  m
-/
#guard_msgs in #print fnNonRec
/--
info: fnNonRec.eq_def (n : Nat) :
  fnNonRec n =
    have m : Nat := n + 1;
    m
-/
#guard_msgs in #check fnNonRec.eq_def
/--
info: fnNonRec.eq_unfold :
  fnNonRec = fun n =>
    have m : Nat := n + 1;
    m
-/
#guard_msgs in #check fnNonRec.eq_unfold


/-!
For theorems, the proof doesn't get transformed, but the type does.
-/
theorem thm : let n := 1; n = 1 := by
  let m := 1
  intro
  exact Eq.refl m
/--
info: theorem thm : have n : Nat := 1;
n = 1 :=
let m : Nat := 1;
let n : Nat := 1;
Eq.refl m
-/
#guard_msgs in #print thm


/-!
Structural recursion doesn't apply the transformation to the declaration value itself,
but it's done to the type and to the equation lemmas.

The smart unfolding definition has the transformation applied to the value.
-/

def fnStructRec (n : Nat) : let α := Nat; α :=
  match n with
  | 0 => 0
  | n + 1 => id (let m := n + 1; m * fnStructRec n)
/--
info: def fnStructRec : Nat →
  have α : Type := Nat;
  α :=
fun n =>
  Nat.brecOn n fun n f =>
    (match (motive :=
        (n : Nat) →
          Nat.below n →
            let α : Type := Nat;
            α)
        n with
      | 0 => fun x => 0
      | n.succ => fun x =>
        id
          (let m : Nat := n + 1;
          m * x.1))
      f
-/
#guard_msgs in #print fnStructRec
/--
info: fnStructRec.eq_def (n : Nat) :
  fnStructRec n =
    match n with
    | 0 => 0
    | n.succ =>
      id
        (have m : Nat := n + 1;
        m * fnStructRec n)
-/
#guard_msgs in #check fnStructRec.eq_def
/-- info: fnStructRec.eq_1 : fnStructRec 0 = 0 -/
#guard_msgs in #check fnStructRec.eq_1
/--
info: fnStructRec.eq_2 (n_2 : Nat) :
  fnStructRec n_2.succ =
    id
      (have m : Nat := n_2 + 1;
      m * fnStructRec n_2)
-/
#guard_msgs in #check fnStructRec.eq_2
/--
info: def fnStructRec._sunfold : Nat →
  have α : Type := Nat;
  α :=
fun n =>
  match n with
  | 0 => 0
  | n.succ =>
    id
      (have m : Nat := n + 1;
      m * fnStructRec n)
-/
#guard_msgs in #print fnStructRec._sunfold

/-!
Smart unfolding check
-/
open Lean Elab Command in
elab "#unfold1 " t:term : command => do
  runTermElabM fun _ => do
    let e ← Term.withSynthesize <| Term.elabTerm t none
    let e? ← Meta.unfoldDefinition? e
    logInfo m!"{e?}"
/-- info: 0 -/
#guard_msgs in #unfold1 fnStructRec 0
/--
info: id
  (have m : Nat := 0 + 1;
  m * fnStructRec 0)
-/
#guard_msgs in #unfold1 fnStructRec 1
/--
info: Nat.brecOn 1 fun n f =>
  (match (motive :=
      (n : Nat) →
        Nat.below n →
          let α : Type := Nat;
          α)
      n with
    | 0 => fun x => 0
    | n.succ => fun x =>
      id
        (let m : Nat := n + 1;
        m * x.1))
    f
-/
#guard_msgs in
set_option smartUnfolding false in
#unfold1 fnStructRec 1


/-!
Well-founded recursion doesn't apply the transformation to the declaration value itself,
but it's done to the type and to the equation lemmas.
-/

def fnWFRec (n : Nat) : let α := Nat; α :=
  match n with
  | 0 => 0
  | n + 1 => id (let m := n + 1; m * fnWFRec (n / 2))
/--
info: @[irreducible] def fnWFRec : Nat →
  have α : Type := Nat;
  α :=
WellFounded.Nat.fix (fun x => x) fun n a =>
  (match (motive :=
      (n : Nat) →
        ((y : Nat) →
            InvImage (fun x1 x2 => x1 < x2) (fun x => x) y n →
              let α : Type := Nat;
              α) →
          let α : Type := Nat;
          α)
      n with
    | 0 => fun x => 0
    | n.succ => fun x =>
      id
        (let m : Nat := n + 1;
        m * x (n / 2) ⋯))
    a
-/
#guard_msgs in #print fnWFRec
/--
info: fnWFRec.eq_def (n : Nat) :
  fnWFRec n =
    match n with
    | 0 => 0
    | n.succ =>
      id
        (have m : Nat := n + 1;
        m * fnWFRec (n / 2))
-/
#guard_msgs in #check fnWFRec.eq_def
/-- info: fnWFRec.eq_1 : fnWFRec 0 = 0 -/
#guard_msgs in #check fnWFRec.eq_1
/--
info: fnWFRec.eq_2 (n_2 : Nat) :
  fnWFRec n_2.succ =
    id
      (have m : Nat := n_2 + 1;
      m * fnWFRec (n_2 / 2))
-/
#guard_msgs in #check fnWFRec.eq_2


/-!
Partial fixedpoint doesn't apply the transformation to the declaration value itself,
but it's done to the type and to the equation lemmas.
-/

def fnPartialFixpoint (n : Nat) : let α := Nat; α :=
  fnPartialFixpoint (let m := n + 1; m)
partial_fixpoint
/--
info: @[irreducible] def fnPartialFixpoint : Nat →
  have α : Type := Nat;
  α :=
Lean.Order.fix
  (fun f n =>
    f
      (let m : Nat := n + 1;
      m))
  fnPartialFixpoint._proof_2
-/
#guard_msgs in #print fnPartialFixpoint
/--
info: fnPartialFixpoint.eq_def (n : Nat) :
  fnPartialFixpoint n =
    fnPartialFixpoint
      (have m : Nat := n + 1;
      m)
-/
#guard_msgs in #check fnPartialFixpoint.eq_def
/--
info: fnPartialFixpoint.eq_1 (n : Nat) :
  fnPartialFixpoint n =
    fnPartialFixpoint
      (have m : Nat := n + 1;
      m)
-/
#guard_msgs in #check fnPartialFixpoint.eq_1


/-!
Do notation, non-recursive.
Note that the pretty printed `let __do_lift`s in the following are from the `do` notation itself;
these are not `let` expressions.
-/
open Lean in
def fnDo (x : MetaM Bool) (y : Nat → MetaM α) : MetaM (Array α) := do
  let a := (← x)
  if a then
    let mut arr := #[]
    for i in *...(10 : Nat) do
      let b := (← y i)
      arr := arr.push b
    return arr
  else
    return #[]
/--
info: def fnDo : {α : Type} → Lean.MetaM Bool → (Nat → Lean.MetaM α) → Lean.MetaM (Array α) :=
fun {α} x y => do
  let __do_lift ← x
  have a : Bool := __do_lift
  if a = true then
      have arr : Array α := #[];
      do
      let r ←
        forIn (*...10) arr fun i r =>
            have arr : Array α := r;
            do
            let __do_lift ← y i
            have b : α := __do_lift
            have arr : Array α := arr.push b
            pure PUnit.unit
            pure (ForInStep.yield arr)
      have arr : Array α := r
      pure arr
    else pure #[]
-/
#guard_msgs in #print fnDo


section
/-!
Tests of cases when `letToHave` is run.
These are verifying that either it's not run, or when there are no `let`s the transformation is skipped.
-/
set_option trace.Meta.letToHave true

/--
trace: [Meta.letToHave] ✅️ no `let` expressions
[Meta.letToHave] ✅️ no `let` expressions
-/
#guard_msgs in
def fnNoLet (n : Nat) := n

-- Not run for `example` at all.
#guard_msgs in
example (n : Nat) := n

/-! Two times, once for `async.commitSignature`, another for `addDecl`, and only on the type. -/
/--
trace: [Meta.letToHave] ✅️ no `let` expressions
---
trace: [Meta.letToHave] ✅️ no `let` expressions
-/
#guard_msgs in
theorem thmNoLet : True := let x := trivial; x
/-! With async disabled, only applied once. -/
/-- trace: [Meta.letToHave] ✅️ no `let` expressions -/
#guard_msgs in
set_option Elab.async false in
theorem thmNoLet' : True := let x := trivial; x

structure A where

/--
trace: [Meta.letToHave] ✅️ no `let` expressions
[Meta.letToHave] ✅️ transformed 1 `let` expressions into `have` expressions
  [Meta.letToHave] result:
        have x : Inhabited A := { default := { } };
        x
-/
#guard_msgs in
instance : Inhabited A := let x := ⟨{}⟩; x

/-! It's a theorem instance. Only applied to the type. -/
/-- trace: [Meta.letToHave] ✅️ no `let` expressions -/
#guard_msgs in
instance : Nonempty A := let x := ⟨{}⟩; x

end

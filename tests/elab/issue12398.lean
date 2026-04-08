inductive PFormula (α: Type): Type where
  | And: Array (PFormula α) → PFormula α
  | Or: Array (PFormula α) → PFormula α
  | Not: (PFormula α) → PFormula α
  | Atom: α → PFormula α
  | FF: PFormula α
  | TT: PFormula α

namespace PFormula

@[simp]
def is_atom (f: PFormula α): Prop :=
  match f with
  | .Atom _ => True
  | _ => False

-- set_option trace.Elab.definition.eqns true
def is_nnf (f: PFormula α): Prop :=
  match f with
  | .And a | .Or a => all_nnf a
  | .Not g => g.is_atom
  | .Atom _ | .TT | .FF => True
  termination_by sizeOf f
where
  all_nnf (a: Array (PFormula α)): Prop := ∀ i, (h: i < a.size) → a[i].is_nnf
  termination_by sizeOf a

-- This is irreducible

/-- info: @[irreducible] def PFormula.is_nnf : {α : Type} → PFormula α → Prop -/
#guard_msgs in
#print sig is_nnf

-- So this should not be defeq!

/-- info: theorem PFormula.is_nnf.eq_4 : ∀ {α : Type} (a : α), (Atom a).is_nnf = True -/
#guard_msgs(pass trace, all) in
#print sig is_nnf.eq_4

-- If we try to prove it manually, it the irreducibility of `is_nnf` prevents that:
theorem eq_4 : ∀ {α : Type} (a : α), (Atom a).is_nnf = True := by
  intros
  fail_if_success rfl -- Should not work
  apply is_nnf.eq_4


def to_nnf (f: PFormula α): PFormula α :=
  match f with
  | .And a => And (a.mapFinIdx (fun i _ _ => a[i].to_nnf))
  | .Or a => Or (a.mapFinIdx (fun i _ _ => a[i].to_nnf))
  | .Not g =>
    match g with
    | .And a => Or (a.mapFinIdx
        (fun i _ _ =>
          have : sizeOf a[i] < sizeOf a := by simp
          (Not a[i]).to_nnf))
    | .Or a => And (a.mapFinIdx
        (fun i _ _ =>
          have : sizeOf a[i] < sizeOf a := by simp
          (Not a[i]).to_nnf))
    | .Not h => h.to_nnf
    | .Atom x => Not (.Atom x)
    | .TT => .FF
    | .FF => .TT
  | g => g

theorem test: (TT: PFormula α).Not.to_nnf.is_nnf := by
  simp [is_nnf, to_nnf]

end PFormula

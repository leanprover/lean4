module
import Lean

/-! Regression tests for #14708: autoParam helpers for section variables must respect visibility. -/

open Lean Meta Elab Command

variable (h : True := by trivial)

public theorem explicitPublic : h = h := rfl
private theorem explicitPrivate : h = h := rfl
theorem defaultPrivate : h = h := rfl

mutual
  public def mutualPublic : h = h := rfl
  def mutualPrivate : h = h := rfl
end

public section

theorem sectionPublic : h = h := rfl
private theorem sectionPrivate : h = h := rfl

public axiom publicAxiom : h = h

example : True.intro = True.intro := explicitPublic
example : True.intro = True.intro := sectionPublic
example : True.intro = True.intro := mutualPublic

run_cmd do
  for decl in [``explicitPublic, ``sectionPublic, ``mutualPublic, ``publicAxiom] do
    let .forallE _ type _ _ := (← getConstInfo decl).type | throwError "expected binder"
    let some (.const helper _) := type.getAutoParamTactic? | throwError "expected helper"
    if isPrivateName helper then
      throwError "public declaration has private helper: {helper}"
    if (← getConstInfo decl).type.hasSorry then
      throwError "unexpected sorry"
  for decl in [``explicitPrivate, ``defaultPrivate, ``sectionPrivate] do
    let .forallE _ type _ _ := (← getConstInfo decl).type | throwError "expected binder"
    let some (.const helper _) := type.getAutoParamTactic? | throwError "expected helper"
    unless isPrivateName helper do
      throwError "private declaration has public helper: {helper}"
  unless isPrivateName ``mutualPrivate do
    throwError "mutual declaration should remain private"
  for exporting in [false, true] do
    withExporting (isExporting := exporting) do
      runTermElabM fun vars => do
        let some (.const helper _) := (← inferType vars[0]!).getAutoParamTactic?
          | throwError "expected helper"
        unless isPrivateName helper == !exporting do
          throwError "helper visibility does not match exporting state"

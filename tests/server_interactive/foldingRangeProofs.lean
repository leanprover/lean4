--^ textDocument/foldingRange
import Lean

/-! Folding ranges of kind `proof` for the values of declarations whose types are propositions. -/

open Lean

theorem oneLineHeader : True := by
  trivial

theorem multiLineHeader (p : Prop) (h : p) :
    p ∧ p := by
  exact ⟨h, h⟩

theorem termOnNextLine : True ∧ True :=
  ⟨trivial,
   trivial⟩

theorem equations : ∀ n : Nat, n + 0 = n
  | 0 => rfl
  | _ + 1 => rfl

theorem oneLine : True := trivial

/--
A doc comment.
-/
theorem withDocComment : True := by
  trivial

theorem withWhere : True := aux
where
  aux : True := trivial

theorem withError : True := by
  exact 0

syntax (name := lemma) declModifiers group("lemma " declId ppIndent(declSig) declVal) : command

@[macro «lemma»] def expandLemma : Macro := fun stx =>
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration

lemma viaLemma : True := by
  trivial

instance propInstance : Nonempty Nat := by
  exact ⟨0⟩

instance dataInstance : Inhabited Nat := by
  exact ⟨0⟩

def dataDef : Nat := by
  exact 0

def propDef : True := by
  trivial

example : Nat := by
  exact 0

example : True := by
  trivial

set_option Elab.async false in
theorem sync : True := by
  trivial

mutual
  theorem mutualA : True := by
    trivial
  theorem mutualB : True := by
    trivial
end

namespace Ns

private theorem privateThm : True := by
  trivial

end Ns

theorem Ns.namespaced : True := by
  trivial

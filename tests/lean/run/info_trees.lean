-- This tests the `#info_trees in` command.
-- If it proves too fragile to test the result using `#guard_msgs`,
-- it is fine to simply remove the `#guard_msgs` and expected output.

/--
info: • [Command] @ ⟨77, 0⟩-⟨77, 40⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] Nat : Type @ ⟨77, 15⟩-⟨77, 18⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Nat : some Sort.{?_uniq.1} @ ⟨77, 15⟩-⟨77, 18⟩
    • [Term] Nat : Type @ ⟨77, 15⟩-⟨77, 18⟩
  • [Term] n (isBinder := true) : Nat @ ⟨77, 11⟩-⟨77, 12⟩
  • [Term] 0 ≤ n : Prop @ ⟨77, 22⟩-⟨77, 27⟩ @ «_aux_Init_Notation___macroRules_term_≤__2»
    • [MacroExpansion]
      0 ≤ n
      ===>
      binrel% LE.le✝ 0 n
      • [Term] 0 ≤ n : Prop @ ⟨77, 22⟩†-⟨77, 27⟩† @ Lean.Elab.Term.Op.elabBinRel
        • [Term] 0 ≤ n : Prop @ ⟨77, 22⟩†-⟨77, 27⟩†
          • [Completion-Id] LE.le✝ : none @ ⟨77, 22⟩†-⟨77, 27⟩†
          • [Term] 0 : Nat @ ⟨77, 22⟩-⟨77, 23⟩ @ Lean.Elab.Term.elabNumLit
          • [Term] n : Nat @ ⟨77, 26⟩-⟨77, 27⟩ @ Lean.Elab.Term.elabIdent
            • [Completion-Id] n : none @ ⟨77, 26⟩-⟨77, 27⟩
            • [Term] n : Nat @ ⟨77, 26⟩-⟨77, 27⟩
  • [CustomInfo(Lean.Elab.Term.AsyncBodyInfo)]
    • [Term] t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨77, 8⟩-⟨77, 9⟩
    • [Term] n (isBinder := true) : Nat @ ⟨77, 11⟩-⟨77, 12⟩
    • [CustomInfo(Lean.Elab.Term.BodyInfo)]
      • [Tactic] @ ⟨77, 31⟩-⟨77, 40⟩
        (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])))
        before ⏎
        n : Nat
        ⊢ 0 ≤ n
        after no goals
        • [Tactic] @ ⟨77, 31⟩-⟨77, 33⟩
          "by"
          before ⏎
          n : Nat
          ⊢ 0 ≤ n
          after no goals
          • [Tactic] @ ⟨77, 34⟩-⟨77, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])]))
            before ⏎
            n : Nat
            ⊢ 0 ≤ n
            after no goals
            • [Tactic] @ ⟨77, 34⟩-⟨77, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq1Indented
              (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])
              before ⏎
              n : Nat
              ⊢ 0 ≤ n
              after no goals
              • [Tactic] @ ⟨77, 34⟩-⟨77, 40⟩ @ Lean.Elab.LibrarySearch.evalExact
                (Tactic.exact? "exact?" [])
                before ⏎
                n : Nat
                ⊢ 0 ≤ n
                after no goals
                • [Tactic] @ ⟨77, 34⟩†-⟨77, 40⟩† @ Lean.Elab.Tactic.evalExact
                  (Tactic.exact "exact" (Term.app `Nat.zero_le [`n]))
                  before ⏎
                  n : Nat
                  ⊢ 0 ≤ n
                  after no goals
                  • [Term] Nat.zero_le n : 0 ≤ n @ ⟨1, 1⟩†-⟨1, 1⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Nat.zero_le : some LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) _uniq.37 @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • [Term] Nat.zero_le : ∀ (n : Nat), 0 ≤ n @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • [Term] n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩† @ Lean.Elab.Term.elabIdent
                      • [Completion-Id] n : some Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
                      • [Term] n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
                • [CustomInfo(Lean.Meta.Tactic.TryThis.TryThisInfo)]
    • [Term] t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨77, 8⟩-⟨77, 9⟩
---
info: Try this:
  exact Nat.zero_le n
-/
#guard_msgs in
#info_trees in
theorem t (n : Nat) : 0 ≤ n := by exact?

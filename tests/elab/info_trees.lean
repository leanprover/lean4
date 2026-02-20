-- This tests the `#info_trees in` command.
-- If it proves too fragile to test the result using `#guard_msgs`,
-- it is fine to simply remove the `#guard_msgs` and expected output.

/--
info: • [Command] @ ⟨79, 0⟩-⟨79, 40⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] Nat : Type @ ⟨79, 15⟩-⟨79, 18⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Nat : some Sort.{?_uniq.1} @ ⟨79, 15⟩-⟨79, 18⟩
    • [Term] Nat : Type @ ⟨79, 15⟩-⟨79, 18⟩
  • [Term] n (isBinder := true) : Nat @ ⟨79, 11⟩-⟨79, 12⟩
  • [Term] 0 ≤ n : Prop @ ⟨79, 22⟩-⟨79, 27⟩ @ «_aux_Init_Notation___macroRules_term_≤__2»
    • [MacroExpansion]
      0 ≤ n
      ===>
      binrel% LE.le✝ 0 n
      • [Term] 0 ≤ n : Prop @ ⟨79, 22⟩†-⟨79, 27⟩† @ Lean.Elab.Term.Op.elabBinRel
        • [Term] 0 ≤ n : Prop @ ⟨79, 22⟩†-⟨79, 27⟩†
          • [Completion-Id] LE.le✝ : none @ ⟨79, 22⟩†-⟨79, 27⟩†
          • [Term] 0 : Nat @ ⟨79, 22⟩-⟨79, 23⟩ @ Lean.Elab.Term.elabNumLit
          • [Term] n : Nat @ ⟨79, 26⟩-⟨79, 27⟩ @ Lean.Elab.Term.elabIdent
            • [Completion-Id] n : none @ ⟨79, 26⟩-⟨79, 27⟩
            • [Term] n : Nat @ ⟨79, 26⟩-⟨79, 27⟩
  • [CustomInfo(Lean.Elab.Term.AsyncBodyInfo)]
    • [Term] n (isBinder := true) : Nat @ ⟨79, 11⟩-⟨79, 12⟩
    • [CustomInfo(Lean.Elab.Term.BodyInfo)]
      • [Tactic] @ ⟨79, 31⟩-⟨79, 40⟩
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" (Tactic.optConfig []) [])])))
        before ⏎
        n : Nat
        ⊢ 0 ≤ n
        after no goals
        • [Tactic] @ ⟨79, 31⟩-⟨79, 33⟩
          "by"
          before ⏎
          n : Nat
          ⊢ 0 ≤ n
          after no goals
          • [Tactic] @ ⟨79, 34⟩-⟨79, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" (Tactic.optConfig []) [])]))
            before ⏎
            n : Nat
            ⊢ 0 ≤ n
            after no goals
            • [Tactic] @ ⟨79, 34⟩-⟨79, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq1Indented
              (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" (Tactic.optConfig []) [])])
              before ⏎
              n : Nat
              ⊢ 0 ≤ n
              after no goals
              • [Tactic] @ ⟨79, 34⟩-⟨79, 40⟩ @ Lean.Elab.LibrarySearch.evalExact
                (Tactic.exact? "exact?" (Tactic.optConfig []) [])
                before ⏎
                n : Nat
                ⊢ 0 ≤ n
                after no goals
                • [Tactic] @ ⟨79, 34⟩†-⟨79, 40⟩† @ Lean.Elab.Tactic.evalExact
                  (Tactic.exact "exact" (Term.app `Nat.zero_le [`n]))
                  before ⏎
                  n : Nat
                  ⊢ 0 ≤ n
                  after no goals
                  • [Term] Nat.zero_le n : 0 ≤ n @ ⟨1, 1⟩†-⟨1, 1⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Nat.zero_le : some LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) _uniq.35.3 @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • [Term] Nat.zero_le : ∀ (n : Nat), 0 ≤ n @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • [Term] n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩† @ Lean.Elab.Term.elabIdent
                      • [Completion-Id] n : some Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
                      • [Term] n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
                • [CustomInfo(Lean.Meta.Tactic.TryThis.TryThisInfo)]
    • [Term] t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨79, 8⟩-⟨79, 9⟩
    • [Term] t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨79, 8⟩-⟨79, 9⟩
---
info: Try this:
  [apply] exact Nat.zero_le n
-/
#guard_msgs in
#info_trees in
theorem t (n : Nat) : 0 ≤ n := by exact?

-- This tests the `#info_trees in` command.
-- If it proves too fragile to test the result using `#guard_msgs`,
-- it is fine to simply remove the `#guard_msgs` and expected output.

/--
info: Try this: exact Nat.zero_le n
---
info: • command @ ⟨81, 0⟩-⟨81, 40⟩ @ Lean.Elab.Command.elabDeclaration
  • Nat : Type @ ⟨81, 15⟩-⟨81, 18⟩ @ Lean.Elab.Term.elabIdent
    • [.] Nat : some Sort.{?_uniq.1} @ ⟨81, 15⟩-⟨81, 18⟩
    • Nat : Type @ ⟨81, 15⟩-⟨81, 18⟩
  • n (isBinder := true) : Nat @ ⟨81, 11⟩-⟨81, 12⟩
  • 0 ≤ n : Prop @ ⟨81, 22⟩-⟨81, 27⟩ @ «_aux_Init_Notation___macroRules_term_≤__2»
    • Macro expansion
      0 ≤ n
      ===>
      binrel% LE.le✝ 0 n
      • 0 ≤ n : Prop @ ⟨81, 22⟩†-⟨81, 27⟩† @ Lean.Elab.Term.Op.elabBinRel
        • 0 ≤ n : Prop @ ⟨81, 22⟩†-⟨81, 27⟩†
          • [.] LE.le✝ : none @ ⟨81, 22⟩†-⟨81, 27⟩†
          • 0 : Nat @ ⟨81, 22⟩-⟨81, 23⟩ @ Lean.Elab.Term.elabNumLit
          • n : Nat @ ⟨81, 26⟩-⟨81, 27⟩ @ Lean.Elab.Term.elabIdent
            • [.] n : none @ ⟨81, 26⟩-⟨81, 27⟩
            • n : Nat @ ⟨81, 26⟩-⟨81, 27⟩
  • t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨81, 8⟩-⟨81, 9⟩
  • n (isBinder := true) : Nat @ ⟨81, 11⟩-⟨81, 12⟩
  • CustomInfo(Lean.Elab.Term.BodyInfo)
    • Tactic @ ⟨81, 31⟩-⟨81, 40⟩
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])))
      before ⏎
      n : Nat
      ⊢ 0 ≤ n
      after no goals
      • Tactic @ ⟨81, 31⟩-⟨81, 33⟩
        "by"
        before ⏎
        n : Nat
        ⊢ 0 ≤ n
        after no goals
        • Tactic @ ⟨81, 34⟩-⟨81, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])]))
          before ⏎
          n : Nat
          ⊢ 0 ≤ n
          after no goals
          • Tactic @ ⟨81, 34⟩-⟨81, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq1Indented
            (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])
            before ⏎
            n : Nat
            ⊢ 0 ≤ n
            after no goals
            • Tactic @ ⟨81, 34⟩-⟨81, 40⟩ @ Lean.Elab.LibrarySearch.evalExact
              (Tactic.exact? "exact?" [])
              before ⏎
              n : Nat
              ⊢ 0 ≤ n
              after no goals
              • Tactic @ ⟨81, 34⟩†-⟨81, 40⟩† @ Lean.Elab.Tactic.evalExact
                (Tactic.exact "exact" (Term.app `Nat.zero_le [`n]))
                before ⏎
                n : Nat
                ⊢ 0 ≤ n
                after no goals
                • Nat.zero_le n : 0 ≤ n @ ⟨1, 1⟩†-⟨1, 1⟩† @ Lean.Elab.Term.elabApp
                  • [.] Nat.zero_le : some LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) _uniq.36 @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • Nat.zero_le : ∀ (n : Nat), 0 ≤ n @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩† @ Lean.Elab.Term.elabIdent
                    • [.] n : some Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
                    • n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
              • CustomInfo(Lean.Meta.Tactic.TryThis.TryThisInfo)
              • UserWidget Lean.Meta.Tactic.TryThis.tryThisWidget
                {"suggestions": [{"suggestion": "exact Nat.zero_le n"}],
                 "style": null,
                 "range":
                 {"start": {"line": 80, "character": 34}, "end": {"line": 80, "character": 40}},
                 "isInline": true,
                 "header": "Try this: "} • t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨81, 8⟩-⟨81, 9⟩
-/
#guard_msgs in
#info_trees in
theorem t (n : Nat) : 0 ≤ n := by exact?

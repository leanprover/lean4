-- This tests the `#info_trees in` command.
-- If it proves too fragile to test the result using `#guard_msgs`,
-- it is fine to simply remove the `#guard_msgs` and expected output.

/--
info: Try this: exact Nat.zero_le n
---
info: • command @ ⟨69, 0⟩-⟨69, 40⟩ @ Lean.Elab.Command.elabDeclaration
  • Nat : Type @ ⟨69, 15⟩-⟨69, 18⟩ @ Lean.Elab.Term.elabIdent
    • [.] Nat : some Sort.{?_uniq.1} @ ⟨69, 15⟩-⟨69, 18⟩
    • Nat : Type @ ⟨69, 15⟩-⟨69, 18⟩
  • n (isBinder := true) : Nat @ ⟨69, 11⟩-⟨69, 12⟩
  • 0 ≤ n : Prop @ ⟨69, 22⟩-⟨69, 27⟩ @ «_aux_Init_Notation___macroRules_term_≤__2»
    • Macro expansion
      0 ≤ n
      ===>
      binrel% LE.le✝ 0 n
      • 0 ≤ n : Prop @ ⟨69, 22⟩†-⟨69, 27⟩† @ Lean.Elab.Term.Op.elabBinRel
        • 0 ≤ n : Prop @ ⟨69, 22⟩†-⟨69, 27⟩†
          • [.] LE.le✝ : none @ ⟨69, 22⟩†-⟨69, 27⟩†
          • 0 : Nat @ ⟨69, 22⟩-⟨69, 23⟩ @ Lean.Elab.Term.elabNumLit
          • n : Nat @ ⟨69, 26⟩-⟨69, 27⟩ @ Lean.Elab.Term.elabIdent
            • [.] n : none @ ⟨69, 26⟩-⟨69, 27⟩
            • n : Nat @ ⟨69, 26⟩-⟨69, 27⟩
  • t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨69, 8⟩-⟨69, 9⟩
  • n (isBinder := true) : Nat @ ⟨69, 11⟩-⟨69, 12⟩
  • CustomInfo(Lean.Elab.Term.BodyInfo)
    • Tactic @ ⟨69, 31⟩-⟨69, 40⟩
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])))
      before ⏎
      n : Nat
      ⊢ 0 ≤ n
      after no goals
      • Tactic @ ⟨69, 31⟩-⟨69, 33⟩
        "by"
        before ⏎
        n : Nat
        ⊢ 0 ≤ n
        after no goals
        • Tactic @ ⟨69, 34⟩-⟨69, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])]))
          before ⏎
          n : Nat
          ⊢ 0 ≤ n
          after no goals
          • Tactic @ ⟨69, 34⟩-⟨69, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq1Indented
            (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])
            before ⏎
            n : Nat
            ⊢ 0 ≤ n
            after no goals
            • Tactic @ ⟨69, 34⟩-⟨69, 40⟩ @ Lean.Elab.LibrarySearch.evalExact
              (Tactic.exact? "exact?" [])
              before ⏎
              n : Nat
              ⊢ 0 ≤ n
              after no goals
              • CustomInfo(Lean.Meta.Tactic.TryThis.TryThisInfo)
              • UserWidget Lean.Meta.Tactic.TryThis.tryThisWidget
                {"suggestions": [{"suggestion": "exact Nat.zero_le n"}],
                 "style": null,
                 "range":
                 {"start": {"line": 68, "character": 34}, "end": {"line": 68, "character": 40}},
                 "isInline": true,
                 "header": "Try this: "} • t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨69, 8⟩-⟨69, 9⟩
-/
#guard_msgs in
#info_trees in
theorem t (n : Nat) : 0 ≤ n := by exact?

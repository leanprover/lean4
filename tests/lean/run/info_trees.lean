-- This tests the `#info_trees in` command.
-- If it proves too fragile to test the result using `#guard_msgs`,
-- it is fine to simply remove the `#guard_msgs` and expected output.

/--
info: • command @ ⟨82, 0⟩-⟨82, 40⟩ @ Lean.Elab.Command.elabDeclaration
  • Nat : Type @ ⟨82, 15⟩-⟨82, 18⟩ @ Lean.Elab.Term.elabIdent
    • [.] Nat : some Sort.{?_uniq.1} @ ⟨82, 15⟩-⟨82, 18⟩
    • Nat : Type @ ⟨82, 15⟩-⟨82, 18⟩
  • n (isBinder := true) : Nat @ ⟨82, 11⟩-⟨82, 12⟩
  • 0 ≤ n : Prop @ ⟨82, 22⟩-⟨82, 27⟩ @ «_aux_Init_Notation___macroRules_term_≤__2»
    • Macro expansion
      0 ≤ n
      ===>
      binrel% LE.le✝ 0 n
      • 0 ≤ n : Prop @ ⟨82, 22⟩†-⟨82, 27⟩† @ Lean.Elab.Term.Op.elabBinRel
        • 0 ≤ n : Prop @ ⟨82, 22⟩†-⟨82, 27⟩†
          • [.] LE.le✝ : none @ ⟨82, 22⟩†-⟨82, 27⟩†
          • 0 : Nat @ ⟨82, 22⟩-⟨82, 23⟩ @ Lean.Elab.Term.elabNumLit
          • n : Nat @ ⟨82, 26⟩-⟨82, 27⟩ @ Lean.Elab.Term.elabIdent
            • [.] n : none @ ⟨82, 26⟩-⟨82, 27⟩
            • n : Nat @ ⟨82, 26⟩-⟨82, 27⟩
  • CustomInfo(Lean.Elab.Term.AsyncBodyInfo)
    • t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨82, 8⟩-⟨82, 9⟩
    • n (isBinder := true) : Nat @ ⟨82, 11⟩-⟨82, 12⟩
    • CustomInfo(Lean.Elab.Term.BodyInfo)
      • Tactic @ ⟨82, 31⟩-⟨82, 40⟩
        (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])))
        before ⏎
        n : Nat
        ⊢ 0 ≤ n
        after no goals
        • Tactic @ ⟨82, 31⟩-⟨82, 33⟩
          "by"
          before ⏎
          n : Nat
          ⊢ 0 ≤ n
          after no goals
          • Tactic @ ⟨82, 34⟩-⟨82, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])]))
            before ⏎
            n : Nat
            ⊢ 0 ≤ n
            after no goals
            • Tactic @ ⟨82, 34⟩-⟨82, 40⟩ @ Lean.Elab.Tactic.evalTacticSeq1Indented
              (Tactic.tacticSeq1Indented [(Tactic.exact? "exact?" [])])
              before ⏎
              n : Nat
              ⊢ 0 ≤ n
              after no goals
              • Tactic @ ⟨82, 34⟩-⟨82, 40⟩ @ Lean.Elab.LibrarySearch.evalExact
                (Tactic.exact? "exact?" [])
                before ⏎
                n : Nat
                ⊢ 0 ≤ n
                after no goals
                • Tactic @ ⟨82, 34⟩†-⟨82, 40⟩† @ Lean.Elab.Tactic.evalExact
                  (Tactic.exact "exact" (Term.app `Nat.zero_le [`n]))
                  before ⏎
                  n : Nat
                  ⊢ 0 ≤ n
                  after no goals
                  • Nat.zero_le n : 0 ≤ n @ ⟨1, 1⟩†-⟨1, 1⟩† @ Lean.Elab.Term.elabApp
                    • [.] Nat.zero_le : some LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) _uniq.41 @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • Nat.zero_le : ∀ (n : Nat), 0 ≤ n @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩† @ Lean.Elab.Term.elabIdent
                      • [.] n : some Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
                      • n : Nat @ ⟨1, 5⟩†-⟨1, 5⟩†
                • CustomInfo(Lean.Meta.Tactic.TryThis.TryThisInfo)
                • UserWidget Lean.Meta.Tactic.TryThis.tryThisWidget
                  {"suggestions": [{"suggestion": "exact Nat.zero_le n"}],
                   "style": null,
                   "range":
                   {"start": {"line": 81, "character": 34}, "end": {"line": 81, "character": 40}},
                   "isInline": true,
                   "header": "Try this: "} • t (isBinder := true) : ∀ (n : Nat), 0 ≤ n @ ⟨82, 8⟩-⟨82, 9⟩
---
info: Try this: exact Nat.zero_le n
-/
#guard_msgs in
#info_trees in
theorem t (n : Nat) : 0 ≤ n := by exact?

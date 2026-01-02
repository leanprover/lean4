import Lean
open Lean

set_option linter.unusedVariables false
set_option guard_msgs.diff false

/--
info: • [Command] @ ⟨107, 0⟩-⟨110, 14⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] Syntax : Type @ ⟨107, 22⟩-⟨107, 28⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Syntax : some Sort.{?_uniq.1} @ ⟨107, 22⟩-⟨107, 28⟩
    • [Term] Syntax : Type @ ⟨107, 22⟩-⟨107, 28⟩
  • [Term] stx (isBinder := true) : Syntax @ ⟨107, 16⟩-⟨107, 19⟩
  • [Term] Bool : Type @ ⟨107, 32⟩-⟨107, 36⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Bool : some Sort.{?_uniq.3} @ ⟨107, 32⟩-⟨107, 36⟩
    • [Term] Bool : Type @ ⟨107, 32⟩-⟨107, 36⟩
  • [Term] stx (isBinder := true) : Syntax @ ⟨107, 16⟩-⟨107, 19⟩
  • [CustomInfo(Lean.Elab.Term.BodyInfo)]
    • [Term] have __discr := stx;
      bif false || __discr.isOfKind `num then
        have x := { raw := __discr };
        true
      else
        have __discr := stx;
        false : Bool @ ⟨108, 2⟩-⟨110, 14⟩ @ Lean.Elab.Term.Quotation.elabMatchSyntax
      • [MacroExpansion]
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        ===>
        have __discr✝ := stx;
        cond✝ (or✝ false✝ (Syntax.isOfKind✝ __discr✝ `num))
          (have x := @TSyntax.mk✝ (List.cons✝ `num List.nil✝) __discr✝;
          true)
          (have __discr✝¹ := stx;
          false)
        • [Term] have __discr := stx;
          bif false || __discr.isOfKind `num then
            have x := { raw := __discr };
            true
          else
            have __discr := stx;
            false : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabHaveDecl
          • [Term] Syntax : Type @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabHole
          • [Term] stx : Syntax @ ⟨108, 8⟩-⟨108, 11⟩ @ Lean.Elab.Term.elabIdent
            • [Completion-Id] stx : some ?_uniq.7 @ ⟨108, 8⟩-⟨108, 11⟩
            • [Term] stx : Syntax @ ⟨108, 8⟩-⟨108, 11⟩
          • [Term] __discr✝ (isBinder := true) : Syntax @ ⟨108, 2⟩†-⟨110, 14⟩†
          • [Term] bif false || __discr✝.isOfKind `num then
              have x := { raw := __discr✝ };
              true
            else
              have __discr := stx;
              false : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabApp
            • [Completion-Id] cond✝ : some Bool @ ⟨108, 2⟩†-⟨110, 14⟩†
            • [Term] @cond : {α : Type} → Bool → α → α → α @ ⟨108, 2⟩†-⟨110, 14⟩†
            • [Term] false || __discr✝.isOfKind `num : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabApp
              • [Completion-Id] or✝ : some Bool @ ⟨108, 2⟩†-⟨110, 14⟩†
              • [Term] or : Bool → Bool → Bool @ ⟨108, 2⟩†-⟨110, 14⟩†
              • [Term] false : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabIdent
                • [Completion-Id] false✝ : some Bool @ ⟨108, 2⟩†-⟨110, 14⟩†
                • [Term] false : Bool @ ⟨108, 2⟩†-⟨110, 14⟩†
              • [Term] __discr✝.isOfKind `num : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.expandParen
                • [MacroExpansion]
                  (Syntax.isOfKind✝ __discr✝ `num)
                  ===>
                  Syntax.isOfKind✝ __discr✝ `num
                  • [Term] __discr✝.isOfKind `num : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Syntax.isOfKind✝ : some Bool @ ⟨108, 2⟩†-⟨110, 14⟩†
                    • [Term] Syntax.isOfKind : Syntax → SyntaxNodeKind → Bool @ ⟨108, 2⟩†-⟨110, 14⟩†
                    • [Term] __discr✝ : Syntax @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabIdent
                      • [Completion-Id] __discr✝ : some Lean.Syntax @ ⟨108, 2⟩†-⟨110, 14⟩†
                      • [Term] __discr✝ : Syntax @ ⟨108, 2⟩†-⟨110, 14⟩†
                    • [Term] `num : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
            • [Term] have x := { raw := __discr✝ };
              true : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabHaveDecl
              • [Term] TSyntax `num : Type @ ⟨109, 7⟩†-⟨109, 8⟩† @ Lean.Elab.Term.elabHole
              • [Term] { raw := __discr✝ } : TSyntax `num @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabApp
                • [Completion-Id] TSyntax.mk✝ : some ?_uniq.12 @ ⟨108, 2⟩†-⟨110, 14⟩†
                • [Term] @TSyntax.mk : {ks : SyntaxNodeKinds} → Syntax → TSyntax ks @ ⟨108, 2⟩†-⟨110, 14⟩†
                • [Term] [`num] : List SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabApp
                  • [Completion-Id] List.cons✝ : some Lean.SyntaxNodeKinds @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • [Term] @List.cons : {α : Type} → α → List α → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • [Term] `num : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                  • [Term] [] : List SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabIdent
                    • [Completion-Id] List.nil✝ : some List.{?_uniq.13} ?_uniq.14 @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • [Term] @List.nil : {α : Type} → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                • [Term] __discr✝ : Syntax @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabIdent
                  • [Completion-Id] __discr✝ : some Lean.Syntax @ ⟨108, 2⟩†-⟨110, 14⟩†
                  • [Term] __discr✝ : Syntax @ ⟨108, 2⟩†-⟨110, 14⟩†
              • [Term] x (isBinder := true) : TSyntax `num @ ⟨109, 7⟩-⟨109, 8⟩
              • [Term] true : Bool @ ⟨109, 17⟩-⟨109, 21⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] true : some ?_uniq.10 @ ⟨109, 17⟩-⟨109, 21⟩
                • [Term] true : Bool @ ⟨109, 17⟩-⟨109, 21⟩
            • [Term] have __discr := stx;
              false : Bool @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabHaveDecl
              • [Term] Syntax : Type @ ⟨108, 2⟩†-⟨110, 14⟩† @ Lean.Elab.Term.elabHole
              • [Term] stx : Syntax @ ⟨108, 8⟩-⟨108, 11⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] stx : some ?_uniq.20 @ ⟨108, 8⟩-⟨108, 11⟩
                • [Term] stx : Syntax @ ⟨108, 8⟩-⟨108, 11⟩
              • [Term] __discr✝ (isBinder := true) : Syntax @ ⟨108, 2⟩†-⟨110, 14⟩†
              • [Term] false : Bool @ ⟨110, 9⟩-⟨110, 14⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] false : some ?_uniq.10 @ ⟨110, 9⟩-⟨110, 14⟩
                • [Term] false : Bool @ ⟨110, 9⟩-⟨110, 14⟩
  • [Term] matchesNum (isBinder := true) : Syntax → Bool @ ⟨107, 4⟩-⟨107, 14⟩
  • [Term] matchesNum (isBinder := true) : Syntax → Bool @ ⟨107, 4⟩-⟨107, 14⟩
-/
#guard_msgs in
#info_trees in
def matchesNum (stx : Syntax) : Bool :=
  match stx with
  | `($x:num) => true
  | _ => false

/--
info: • [Command] @ ⟨212, 0⟩-⟨215, 14⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] Syntax : Type @ ⟨212, 24⟩-⟨212, 30⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Syntax : some Sort.{?_uniq.28} @ ⟨212, 24⟩-⟨212, 30⟩
    • [Term] Syntax : Type @ ⟨212, 24⟩-⟨212, 30⟩
  • [Term] stx (isBinder := true) : Syntax @ ⟨212, 18⟩-⟨212, 21⟩
  • [Term] Bool : Type @ ⟨212, 34⟩-⟨212, 38⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Bool : some Sort.{?_uniq.30} @ ⟨212, 34⟩-⟨212, 38⟩
    • [Term] Bool : Type @ ⟨212, 34⟩-⟨212, 38⟩
  • [Term] stx (isBinder := true) : Syntax @ ⟨212, 18⟩-⟨212, 21⟩
  • [CustomInfo(Lean.Elab.Term.BodyInfo)]
    • [Term] have __discr := stx;
      bif false || __discr.isOfKind `ident then
        have x := { raw := __discr };
        true
      else
        have __discr := stx;
        false : Bool @ ⟨213, 2⟩-⟨215, 14⟩ @ Lean.Elab.Term.Quotation.elabMatchSyntax
      • [MacroExpansion]
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        ===>
        have __discr✝ := stx;
        cond✝ (or✝ false✝ (Syntax.isOfKind✝ __discr✝ `ident))
          (have x := @TSyntax.mk✝ (List.cons✝ `ident List.nil✝) __discr✝;
          true)
          (have __discr✝¹ := stx;
          false)
        • [Term] have __discr := stx;
          bif false || __discr.isOfKind `ident then
            have x := { raw := __discr };
            true
          else
            have __discr := stx;
            false : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabHaveDecl
          • [Term] Syntax : Type @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabHole
          • [Term] stx : Syntax @ ⟨213, 8⟩-⟨213, 11⟩ @ Lean.Elab.Term.elabIdent
            • [Completion-Id] stx : some ?_uniq.34 @ ⟨213, 8⟩-⟨213, 11⟩
            • [Term] stx : Syntax @ ⟨213, 8⟩-⟨213, 11⟩
          • [Term] __discr✝ (isBinder := true) : Syntax @ ⟨213, 2⟩†-⟨215, 14⟩†
          • [Term] bif false || __discr✝.isOfKind `ident then
              have x := { raw := __discr✝ };
              true
            else
              have __discr := stx;
              false : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabApp
            • [Completion-Id] cond✝ : some Bool @ ⟨213, 2⟩†-⟨215, 14⟩†
            • [Term] @cond : {α : Type} → Bool → α → α → α @ ⟨213, 2⟩†-⟨215, 14⟩†
            • [Term] false || __discr✝.isOfKind `ident : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabApp
              • [Completion-Id] or✝ : some Bool @ ⟨213, 2⟩†-⟨215, 14⟩†
              • [Term] or : Bool → Bool → Bool @ ⟨213, 2⟩†-⟨215, 14⟩†
              • [Term] false : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabIdent
                • [Completion-Id] false✝ : some Bool @ ⟨213, 2⟩†-⟨215, 14⟩†
                • [Term] false : Bool @ ⟨213, 2⟩†-⟨215, 14⟩†
              • [Term] __discr✝.isOfKind `ident : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.expandParen
                • [MacroExpansion]
                  (Syntax.isOfKind✝ __discr✝ `ident)
                  ===>
                  Syntax.isOfKind✝ __discr✝ `ident
                  • [Term] __discr✝.isOfKind `ident : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Syntax.isOfKind✝ : some Bool @ ⟨213, 2⟩†-⟨215, 14⟩†
                    • [Term] Syntax.isOfKind : Syntax → SyntaxNodeKind → Bool @ ⟨213, 2⟩†-⟨215, 14⟩†
                    • [Term] __discr✝ : Syntax @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabIdent
                      • [Completion-Id] __discr✝ : some Lean.Syntax @ ⟨213, 2⟩†-⟨215, 14⟩†
                      • [Term] __discr✝ : Syntax @ ⟨213, 2⟩†-⟨215, 14⟩†
                    • [Term] `ident : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
            • [Term] have x := { raw := __discr✝ };
              true : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabHaveDecl
              • [Term] TSyntax `ident : Type @ ⟨214, 7⟩†-⟨214, 8⟩† @ Lean.Elab.Term.elabHole
              • [Term] { raw := __discr✝ } : TSyntax `ident @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabApp
                • [Completion-Id] TSyntax.mk✝ : some ?_uniq.39 @ ⟨213, 2⟩†-⟨215, 14⟩†
                • [Term] @TSyntax.mk : {ks : SyntaxNodeKinds} → Syntax → TSyntax ks @ ⟨213, 2⟩†-⟨215, 14⟩†
                • [Term] [`ident] : List SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabApp
                  • [Completion-Id] List.cons✝ : some Lean.SyntaxNodeKinds @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • [Term] @List.cons : {α : Type} → α → List α → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • [Term] `ident : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                  • [Term] [] : List SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabIdent
                    • [Completion-Id] List.nil✝ : some List.{?_uniq.40} ?_uniq.41 @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • [Term] @List.nil : {α : Type} → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                • [Term] __discr✝ : Syntax @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabIdent
                  • [Completion-Id] __discr✝ : some Lean.Syntax @ ⟨213, 2⟩†-⟨215, 14⟩†
                  • [Term] __discr✝ : Syntax @ ⟨213, 2⟩†-⟨215, 14⟩†
              • [Term] x (isBinder := true) : TSyntax `ident @ ⟨214, 7⟩-⟨214, 8⟩
              • [Term] true : Bool @ ⟨214, 19⟩-⟨214, 23⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] true : some ?_uniq.37 @ ⟨214, 19⟩-⟨214, 23⟩
                • [Term] true : Bool @ ⟨214, 19⟩-⟨214, 23⟩
            • [Term] have __discr := stx;
              false : Bool @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabHaveDecl
              • [Term] Syntax : Type @ ⟨213, 2⟩†-⟨215, 14⟩† @ Lean.Elab.Term.elabHole
              • [Term] stx : Syntax @ ⟨213, 8⟩-⟨213, 11⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] stx : some ?_uniq.47 @ ⟨213, 8⟩-⟨213, 11⟩
                • [Term] stx : Syntax @ ⟨213, 8⟩-⟨213, 11⟩
              • [Term] __discr✝ (isBinder := true) : Syntax @ ⟨213, 2⟩†-⟨215, 14⟩†
              • [Term] false : Bool @ ⟨215, 9⟩-⟨215, 14⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] false : some ?_uniq.37 @ ⟨215, 9⟩-⟨215, 14⟩
                • [Term] false : Bool @ ⟨215, 9⟩-⟨215, 14⟩
  • [Term] matchesIdent (isBinder := true) : Syntax → Bool @ ⟨212, 4⟩-⟨212, 16⟩
  • [Term] matchesIdent (isBinder := true) : Syntax → Bool @ ⟨212, 4⟩-⟨212, 16⟩
-/
#guard_msgs in
#info_trees in
def matchesIdent (stx : Syntax) : Bool :=
  match stx with
  | `($x:ident) => true
  | _ => false

/--
info: • [Command] @ ⟨317, 0⟩-⟨320, 14⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] Syntax : Type @ ⟨317, 22⟩-⟨317, 28⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Syntax : some Sort.{?_uniq.55} @ ⟨317, 22⟩-⟨317, 28⟩
    • [Term] Syntax : Type @ ⟨317, 22⟩-⟨317, 28⟩
  • [Term] stx (isBinder := true) : Syntax @ ⟨317, 16⟩-⟨317, 19⟩
  • [Term] Bool : Type @ ⟨317, 32⟩-⟨317, 36⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Bool : some Sort.{?_uniq.57} @ ⟨317, 32⟩-⟨317, 36⟩
    • [Term] Bool : Type @ ⟨317, 32⟩-⟨317, 36⟩
  • [Term] stx (isBinder := true) : Syntax @ ⟨317, 16⟩-⟨317, 19⟩
  • [CustomInfo(Lean.Elab.Term.BodyInfo)]
    • [Term] have __discr := stx;
      bif false || __discr.isOfKind `str then
        have x := { raw := __discr };
        true
      else
        have __discr := stx;
        false : Bool @ ⟨318, 2⟩-⟨320, 14⟩ @ Lean.Elab.Term.Quotation.elabMatchSyntax
      • [MacroExpansion]
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        ===>
        have __discr✝ := stx;
        cond✝ (or✝ false✝ (Syntax.isOfKind✝ __discr✝ `str))
          (have x := @TSyntax.mk✝ (List.cons✝ `str List.nil✝) __discr✝;
          true)
          (have __discr✝¹ := stx;
          false)
        • [Term] have __discr := stx;
          bif false || __discr.isOfKind `str then
            have x := { raw := __discr };
            true
          else
            have __discr := stx;
            false : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabHaveDecl
          • [Term] Syntax : Type @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabHole
          • [Term] stx : Syntax @ ⟨318, 8⟩-⟨318, 11⟩ @ Lean.Elab.Term.elabIdent
            • [Completion-Id] stx : some ?_uniq.61 @ ⟨318, 8⟩-⟨318, 11⟩
            • [Term] stx : Syntax @ ⟨318, 8⟩-⟨318, 11⟩
          • [Term] __discr✝ (isBinder := true) : Syntax @ ⟨318, 2⟩†-⟨320, 14⟩†
          • [Term] bif false || __discr✝.isOfKind `str then
              have x := { raw := __discr✝ };
              true
            else
              have __discr := stx;
              false : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabApp
            • [Completion-Id] cond✝ : some Bool @ ⟨318, 2⟩†-⟨320, 14⟩†
            • [Term] @cond : {α : Type} → Bool → α → α → α @ ⟨318, 2⟩†-⟨320, 14⟩†
            • [Term] false || __discr✝.isOfKind `str : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabApp
              • [Completion-Id] or✝ : some Bool @ ⟨318, 2⟩†-⟨320, 14⟩†
              • [Term] or : Bool → Bool → Bool @ ⟨318, 2⟩†-⟨320, 14⟩†
              • [Term] false : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabIdent
                • [Completion-Id] false✝ : some Bool @ ⟨318, 2⟩†-⟨320, 14⟩†
                • [Term] false : Bool @ ⟨318, 2⟩†-⟨320, 14⟩†
              • [Term] __discr✝.isOfKind `str : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.expandParen
                • [MacroExpansion]
                  (Syntax.isOfKind✝ __discr✝ `str)
                  ===>
                  Syntax.isOfKind✝ __discr✝ `str
                  • [Term] __discr✝.isOfKind `str : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Syntax.isOfKind✝ : some Bool @ ⟨318, 2⟩†-⟨320, 14⟩†
                    • [Term] Syntax.isOfKind : Syntax → SyntaxNodeKind → Bool @ ⟨318, 2⟩†-⟨320, 14⟩†
                    • [Term] __discr✝ : Syntax @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabIdent
                      • [Completion-Id] __discr✝ : some Lean.Syntax @ ⟨318, 2⟩†-⟨320, 14⟩†
                      • [Term] __discr✝ : Syntax @ ⟨318, 2⟩†-⟨320, 14⟩†
                    • [Term] `str : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
            • [Term] have x := { raw := __discr✝ };
              true : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabHaveDecl
              • [Term] TSyntax `str : Type @ ⟨319, 7⟩†-⟨319, 8⟩† @ Lean.Elab.Term.elabHole
              • [Term] { raw := __discr✝ } : TSyntax `str @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabApp
                • [Completion-Id] TSyntax.mk✝ : some ?_uniq.66 @ ⟨318, 2⟩†-⟨320, 14⟩†
                • [Term] @TSyntax.mk : {ks : SyntaxNodeKinds} → Syntax → TSyntax ks @ ⟨318, 2⟩†-⟨320, 14⟩†
                • [Term] [`str] : List SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabApp
                  • [Completion-Id] List.cons✝ : some Lean.SyntaxNodeKinds @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • [Term] @List.cons : {α : Type} → α → List α → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                  • [Term] `str : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                  • [Term] [] : List SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabIdent
                    • [Completion-Id] List.nil✝ : some List.{?_uniq.67} ?_uniq.68 @ ⟨1, 0⟩†-⟨1, 0⟩†
                    • [Term] @List.nil : {α : Type} → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                • [Term] __discr✝ : Syntax @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabIdent
                  • [Completion-Id] __discr✝ : some Lean.Syntax @ ⟨318, 2⟩†-⟨320, 14⟩†
                  • [Term] __discr✝ : Syntax @ ⟨318, 2⟩†-⟨320, 14⟩†
              • [Term] x (isBinder := true) : TSyntax `str @ ⟨319, 7⟩-⟨319, 8⟩
              • [Term] true : Bool @ ⟨319, 17⟩-⟨319, 21⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] true : some ?_uniq.64 @ ⟨319, 17⟩-⟨319, 21⟩
                • [Term] true : Bool @ ⟨319, 17⟩-⟨319, 21⟩
            • [Term] have __discr := stx;
              false : Bool @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabHaveDecl
              • [Term] Syntax : Type @ ⟨318, 2⟩†-⟨320, 14⟩† @ Lean.Elab.Term.elabHole
              • [Term] stx : Syntax @ ⟨318, 8⟩-⟨318, 11⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] stx : some ?_uniq.74 @ ⟨318, 8⟩-⟨318, 11⟩
                • [Term] stx : Syntax @ ⟨318, 8⟩-⟨318, 11⟩
              • [Term] __discr✝ (isBinder := true) : Syntax @ ⟨318, 2⟩†-⟨320, 14⟩†
              • [Term] false : Bool @ ⟨320, 9⟩-⟨320, 14⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] false : some ?_uniq.64 @ ⟨320, 9⟩-⟨320, 14⟩
                • [Term] false : Bool @ ⟨320, 9⟩-⟨320, 14⟩
  • [Term] matchesStr (isBinder := true) : Syntax → Bool @ ⟨317, 4⟩-⟨317, 14⟩
  • [Term] matchesStr (isBinder := true) : Syntax → Bool @ ⟨317, 4⟩-⟨317, 14⟩
-/
#guard_msgs in
#info_trees in
def matchesStr (stx : Syntax) : Bool :=
  match stx with
  | `($x:str) => true
  | _ => false

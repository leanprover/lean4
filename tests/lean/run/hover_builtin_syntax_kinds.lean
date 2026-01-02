import Lean
open Lean

set_option guard_msgs.diff false

/--
info: • [Command] @ ⟨357, 0⟩-⟨359, 22⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] MacroM (TSyntax `term) : Type @ ⟨357, 14⟩-⟨357, 36⟩ @ Lean.Elab.Term.elabApp
    • [Completion-Id] MacroM : some Sort.{?_uniq.1} @ ⟨357, 14⟩-⟨357, 20⟩
    • [Term] MacroM : Type → Type @ ⟨357, 14⟩-⟨357, 20⟩
    • [Term] TSyntax `term : Type @ ⟨357, 21⟩-⟨357, 36⟩ @ Lean.Elab.Term.expandParen
      • [MacroExpansion]
        (TSyntax `term)
        ===>
        TSyntax `term
        • [Term] TSyntax `term : Type @ ⟨357, 22⟩-⟨357, 35⟩ @ Lean.Elab.Term.elabApp
          • [Completion-Id] TSyntax : some Type @ ⟨357, 22⟩-⟨357, 29⟩
          • [Term] TSyntax : SyntaxNodeKinds → Type @ ⟨357, 22⟩-⟨357, 29⟩
          • [Term] `term : Name @ ⟨357, 30⟩-⟨357, 35⟩ @ Lean.Elab.Term.elabQuotedName
          • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
  • [CustomInfo(Lean.Elab.Term.BodyInfo)]
    • [Term] let x := Syntax.mkNumLit "1";
      do
      let __do_lift ←
        do
          let _ ← MonadRef.mkInfoFromRefPos
          let _ ← getCurrMacroScope
          let _ ← MonadQuotation.getContext
          pure { raw := x.raw }
      pure __do_lift : MacroM (TSyntax `term) @ ⟨357, 40⟩-⟨359, 22⟩ @ Lean.Elab.Term.elabDo
      • [Term] MacroM : Type → Type @ ⟨357, 40⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabSyntheticHole
      • [Term] TSyntax `term : Type @ ⟨357, 40⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabSyntheticHole
      • [MacroExpansion]
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        ===>
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        • [Term] let x := Syntax.mkNumLit "1";
          do
          let __do_lift ←
            do
              let _ ← MonadRef.mkInfoFromRefPos
              let _ ← getCurrMacroScope
              let _ ← MonadQuotation.getContext
              pure { raw := x.raw }
          pure __do_lift : MacroM (TSyntax `term) @ ⟨358, 2⟩†-⟨358, 45⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
          • [Term] let x := Syntax.mkNumLit "1";
            do
            let __do_lift ←
              do
                let _ ← MonadRef.mkInfoFromRefPos
                let _ ← getCurrMacroScope
                let _ ← MonadQuotation.getContext
                pure { raw := x.raw }
            pure __do_lift : MacroM (TSyntax `term) @ ⟨358, 2⟩-⟨358, 45⟩
            • [Term] let x := Syntax.mkNumLit "1";
              do
              let __do_lift ←
                do
                  let _ ← MonadRef.mkInfoFromRefPos
                  let _ ← getCurrMacroScope
                  let _ ← MonadQuotation.getContext
                  pure { raw := x.raw }
              pure __do_lift : MacroM (TSyntax `term) @ ⟨358, 2⟩†-⟨358, 45⟩† @ Lean.Elab.Term.elabLetDecl
              • [Term] TSyntax `num : Type @ ⟨358, 10⟩-⟨358, 22⟩ @ Lean.Elab.Term.elabApp
                • [Completion-Id] TSyntax : some Sort.{?_uniq.80} @ ⟨358, 10⟩-⟨358, 17⟩
                • [Term] TSyntax : SyntaxNodeKinds → Type @ ⟨358, 10⟩-⟨358, 17⟩
                • [Term] `num : Name @ ⟨358, 18⟩-⟨358, 22⟩ @ Lean.Elab.Term.elabQuotedName
                • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
              • [Term] Syntax.mkNumLit "1" : NumLit @ ⟨358, 26⟩-⟨358, 45⟩ @ Lean.Elab.Term.elabApp
                • [Completion-Id] Syntax.mkNumLit : some Lean.TSyntax (List.cons.{0} Lean.SyntaxNodeKind (Lean.Name.mkStr1 "num") (List.nil.{0} Lean.SyntaxNodeKind)) @ ⟨358, 26⟩-⟨358, 41⟩
                • [Term] @Syntax.mkNumLit : String → optParam SourceInfo SourceInfo.none → NumLit @ ⟨358, 26⟩-⟨358, 41⟩
                • [Term] "1" : String @ ⟨358, 42⟩-⟨358, 45⟩ @ Lean.Elab.Term.elabStrLit
              • [Term] x (isBinder := true) : TSyntax `num @ ⟨358, 6⟩-⟨358, 7⟩
              • [Term] do
                  let __do_lift ←
                    do
                      let _ ← MonadRef.mkInfoFromRefPos
                      let _ ← getCurrMacroScope
                      let _ ← MonadQuotation.getContext
                      pure { raw := x.raw }
                  pure __do_lift : MacroM (TSyntax `term) @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
                • [Term] do
                    let __do_lift ←
                      do
                        let _ ← MonadRef.mkInfoFromRefPos
                        let _ ← getCurrMacroScope
                        let _ ← MonadQuotation.getContext
                        pure { raw := x.raw }
                    pure __do_lift : MacroM (TSyntax `term) @ ⟨359, 2⟩†-⟨359, 22⟩†
                  • [Term] do
                      let __do_lift ←
                        do
                          let _ ← MonadRef.mkInfoFromRefPos
                          let _ ← getCurrMacroScope
                          let _ ← MonadQuotation.getContext
                          pure { raw := x.raw }
                      pure __do_lift : MacroM (TSyntax `term) @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Bind.bind✝ : some Lean.MacroM (Lean.TSyntax (List.cons.{0} Lean.SyntaxNodeKind (Lean.Name.mkStr1 "term") (List.nil.{0} Lean.SyntaxNodeKind))) @ ⟨359, 2⟩†-⟨359, 22⟩†
                    • [Term] @bind : {m : Type → Type} →
                        [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨359, 2⟩†-⟨359, 22⟩†
                    • [Term] do
                        let _ ← MonadRef.mkInfoFromRefPos
                        let _ ← getCurrMacroScope
                        let _ ← MonadQuotation.getContext
                        pure
                            {
                              raw :=
                                x.raw } : MacroM
                        (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabTypeAscription
                      • [Term] MacroM (TSyntax `term) : Type @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabApp
                        • [Term] MacroM : Type → Type @ ⟨357, 40⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabSyntheticHole
                        • [Term] TSyntax `term : Type @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabHole
                      • [Term] do
                          let _ ← MonadRef.mkInfoFromRefPos
                          let _ ← getCurrMacroScope
                          let _ ← MonadQuotation.getContext
                          pure
                              {
                                raw :=
                                  x.raw } : MacroM
                          (TSyntax
                            `term) @ ⟨359, 12⟩-⟨359, 21⟩ @ Lean.Elab.Term.Quotation.elabQuot._@.Lean.Elab.Quotation.3282600398._hygCtx._hyg.3
                        • [MacroExpansion]
                          failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
                          ===>
                          Bind.bind✝ MonadRef.mkInfoFromRefPos✝
                            (fun info✝ =>
                              Bind.bind✝ getCurrMacroScope✝
                                (fun scp✝ =>
                                  Bind.bind✝ MonadQuotation.getContext✝
                                    (fun quotCtx✝ =>
                                      Pure.pure✝ (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x)))))
                          • [Term] do
                              let _ ← MonadRef.mkInfoFromRefPos
                              let _ ← getCurrMacroScope
                              let _ ← MonadQuotation.getContext
                              pure
                                  {
                                    raw :=
                                      x.raw } : MacroM (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabApp
                            • [Completion-Id] Bind.bind✝ : some ?_uniq.78 ?_uniq.182 @ ⟨359, 12⟩†-⟨359, 21⟩†
                            • [Term] @bind : {m : Type → Type} →
                                [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨359, 12⟩†-⟨359, 21⟩†
                            • [Term] MonadRef.mkInfoFromRefPos : MacroM
                                SourceInfo @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabIdent
                              • [Completion-Id] MonadRef.mkInfoFromRefPos✝ : some ?_uniq.185 ?_uniq.187 @ ⟨359, 12⟩†-⟨359, 21⟩†
                              • [Term] @MonadRef.mkInfoFromRefPos : {m : Type → Type} →
                                  [Monad m] → [MonadRef m] → m SourceInfo @ ⟨359, 12⟩†-⟨359, 21⟩†
                            • [Term] fun info => do
                                let _ ← getCurrMacroScope
                                let _ ← MonadQuotation.getContext
                                pure
                                    {
                                      raw :=
                                        x.raw } : SourceInfo →
                                MacroM (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.expandParen
                              • [MacroExpansion]
                                (fun info✝ =>
                                  Bind.bind✝ getCurrMacroScope✝
                                    (fun scp✝ =>
                                      Bind.bind✝ MonadQuotation.getContext✝
                                        (fun quotCtx✝ =>
                                          Pure.pure✝
                                            (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x)))))
                                ===>
                                fun info✝ =>
                                  Bind.bind✝ getCurrMacroScope✝
                                    (fun scp✝ =>
                                      Bind.bind✝ MonadQuotation.getContext✝
                                        (fun quotCtx✝ =>
                                          Pure.pure✝
                                            (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x))))
                                • [Term] fun info => do
                                    let _ ← getCurrMacroScope
                                    let _ ← MonadQuotation.getContext
                                    pure
                                        {
                                          raw :=
                                            x.raw } : SourceInfo →
                                    MacroM (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabFun
                                  • [Term] SourceInfo : Type @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabHole
                                  • [Term] info✝ (isBinder := true) : SourceInfo @ ⟨359, 12⟩†-⟨359, 21⟩†
                                  • [Term] do
                                      let _ ← getCurrMacroScope
                                      let _ ← MonadQuotation.getContext
                                      pure
                                          {
                                            raw :=
                                              x.raw } : MacroM
                                      (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabApp
                                    • [Completion-Id] Bind.bind✝ : some ?_uniq.185 ?_uniq.188 @ ⟨359, 12⟩†-⟨359, 21⟩†
                                    • [Term] @bind : {m : Type → Type} →
                                        [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨359, 12⟩†-⟨359, 21⟩†
                                    • [Term] getCurrMacroScope : MacroM
                                        MacroScope @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabIdent
                                      • [Completion-Id] getCurrMacroScope✝ : some ?_uniq.280 ?_uniq.282 @ ⟨359, 12⟩†-⟨359, 21⟩†
                                      • [Term] @getCurrMacroScope : {m : Type → Type} →
                                          [self : MonadQuotation m] → m MacroScope @ ⟨359, 12⟩†-⟨359, 21⟩†
                                    • [Term] fun scp => do
                                        let _ ← MonadQuotation.getContext
                                        pure
                                            {
                                              raw :=
                                                x.raw } : MacroScope →
                                        MacroM (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.expandParen
                                      • [MacroExpansion]
                                        (fun scp✝ =>
                                          Bind.bind✝ MonadQuotation.getContext✝
                                            (fun quotCtx✝ =>
                                              Pure.pure✝
                                                (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x))))
                                        ===>
                                        fun scp✝ =>
                                          Bind.bind✝ MonadQuotation.getContext✝
                                            (fun quotCtx✝ =>
                                              Pure.pure✝
                                                (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x)))
                                        • [Term] fun scp => do
                                            let _ ← MonadQuotation.getContext
                                            pure
                                                {
                                                  raw :=
                                                    x.raw } : MacroScope →
                                            MacroM (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabFun
                                          • [Term] MacroScope : Type @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabHole
                                          • [Term] scp✝ (isBinder := true) : MacroScope @ ⟨359, 12⟩†-⟨359, 21⟩†
                                          • [Term] do
                                              let _ ← MonadQuotation.getContext
                                              pure
                                                  {
                                                    raw :=
                                                      x.raw } : MacroM
                                              (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabApp
                                            • [Completion-Id] Bind.bind✝ : some ?_uniq.280 ?_uniq.283 @ ⟨359, 12⟩†-⟨359, 21⟩†
                                            • [Term] @bind : {m : Type → Type} →
                                                [self : Bind m] →
                                                  {α β : Type} → m α → (α → m β) → m β @ ⟨359, 12⟩†-⟨359, 21⟩†
                                            • [Term] MonadQuotation.getContext : MacroM
                                                Name @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabIdent
                                              • [Completion-Id] MonadQuotation.getContext✝ : some ?_uniq.330 ?_uniq.332 @ ⟨359, 12⟩†-⟨359, 21⟩†
                                              • [Term] @MonadQuotation.getContext : {m : Type → Type} →
                                                  [self : MonadQuotation m] → m Name @ ⟨359, 12⟩†-⟨359, 21⟩†
                                            • [Term] fun quotCtx =>
                                                pure
                                                  {
                                                    raw :=
                                                      x.raw } : Name →
                                                MacroM
                                                  (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.expandParen
                                              • [MacroExpansion]
                                                (fun quotCtx✝ =>
                                                  Pure.pure✝
                                                    (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x)))
                                                ===>
                                                fun quotCtx✝ =>
                                                  Pure.pure✝
                                                    (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x))
                                                • [Term] fun quotCtx =>
                                                    pure
                                                      {
                                                        raw :=
                                                          x.raw } : Name →
                                                    MacroM
                                                      (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabFun
                                                  • [Term] Name : Type @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabHole
                                                  • [Term] quotCtx✝ (isBinder := true) : Name @ ⟨359, 12⟩†-⟨359, 21⟩†
                                                  • [Term] pure
                                                      {
                                                        raw :=
                                                          x.raw } : MacroM
                                                      (TSyntax `term) @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabApp
                                                    • [Completion-Id] Pure.pure✝ : some ?_uniq.330 ?_uniq.333 @ ⟨359, 12⟩†-⟨359, 21⟩†
                                                    • [Term] @pure : {f : Type → Type} →
                                                        [self : Pure f] → {α : Type} → α → f α @ ⟨359, 12⟩†-⟨359, 21⟩†
                                                    • [Term] {
                                                        raw :=
                                                          x.raw } : TSyntax
                                                        `term @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.expandParen
                                                      • [MacroExpansion]
                                                        (@TSyntax.mk✝ `term
                                                          (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x))
                                                        ===>
                                                        @TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `num List.nil✝) x)
                                                        • [Term] {
                                                            raw :=
                                                              x.raw } : TSyntax
                                                            `term @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabApp
                                                          • [Completion-Id] TSyntax.mk✝ : some ?_uniq.381 @ ⟨359, 12⟩†-⟨359, 21⟩†
                                                          • [Term] @TSyntax.mk : {ks : SyntaxNodeKinds} →
                                                              Syntax → TSyntax ks @ ⟨359, 12⟩†-⟨359, 21⟩†
                                                          • [Term] `term : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                                                          • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
                                                          • [Term] x.raw : Syntax @ ⟨359, 12⟩†-⟨359, 21⟩† @ Lean.Elab.Term.elabApp
                                                            • [Completion-Id] TSyntax.raw✝ : some Lean.Syntax @ ⟨359, 12⟩†-⟨359, 21⟩†
                                                            • [Term] @TSyntax.raw : {ks : SyntaxNodeKinds} →
                                                                TSyntax ks → Syntax @ ⟨359, 12⟩†-⟨359, 21⟩†
                                                            • [Term] [`num] : List
                                                                SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabApp
                                                              • [Completion-Id] List.cons✝ : some Lean.SyntaxNodeKinds @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                              • [Term] @List.cons : {α : Type} →
                                                                  α → List α → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                              • [Term] `num : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                                                              • [Term] [] : List
                                                                  SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabIdent
                                                                • [Completion-Id] List.nil✝ : some List.{?_uniq.458} ?_uniq.459 @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                                • [Term] @List.nil : {α : Type} →
                                                                    List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                            • [Term] x : TSyntax
                                                                `num @ ⟨359, 15⟩-⟨359, 16⟩ @ Lean.Elab.Term.elabIdent
                                                              • [Completion-Id] x : some Lean.TSyntax (List.cons.{?_uniq.458} ?_uniq.459 (Lean.Name.mkStr1 "num") (List.nil.{?_uniq.460} ?_uniq.461)) @ ⟨359, 15⟩-⟨359, 16⟩
                                                              • [Term] x : TSyntax `num @ ⟨359, 15⟩-⟨359, 16⟩
                    • [Term] fun __do_lift =>
                        pure
                          __do_lift : TSyntax `term →
                        MacroM (TSyntax `term) @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.expandParen
                      • [MacroExpansion]
                        (fun (__do_lift✝ : _) =>
                          with_annotate_term(Term.doReturn
                               "return"
                               [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `__do_lift✝ ")")])
                            Pure.pure✝ (__do_lift✝))
                        ===>
                        fun (__do_lift✝ : _) =>
                          with_annotate_term(Term.doReturn
                               "return"
                               [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `__do_lift✝ ")")])
                            Pure.pure✝ (__do_lift✝)
                        • [Term] fun __do_lift =>
                            pure
                              __do_lift : TSyntax `term →
                            MacroM (TSyntax `term) @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabFun
                          • [Term] TSyntax `term : Type @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabHole
                          • [Term] __do_lift✝ (isBinder := true) : TSyntax `term @ ⟨359, 2⟩†-⟨359, 22⟩†
                          • [Term] pure
                              __do_lift✝ : MacroM
                              (TSyntax `term) @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
                            • [Term] pure __do_lift✝ : MacroM (TSyntax `term) @ ⟨359, 2⟩-⟨359, 22⟩
                              • [Term] pure
                                  __do_lift✝ : MacroM (TSyntax `term) @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabApp
                                • [Completion-Id] Pure.pure✝ : some ?_uniq.140 ?_uniq.143 @ ⟨359, 2⟩†-⟨359, 22⟩†
                                • [Term] @pure : {f : Type → Type} →
                                    [self : Pure f] → {α : Type} → α → f α @ ⟨359, 2⟩†-⟨359, 22⟩†
                                • [Term] __do_lift✝ : TSyntax `term @ ⟨359, 9⟩-⟨359, 22⟩ @ Lean.Elab.Term.expandParen
                                  • [MacroExpansion]
                                    (__do_lift✝)
                                    ===>
                                    __do_lift✝
                                    • [Term] __do_lift✝ : TSyntax
                                        `term @ ⟨359, 2⟩†-⟨359, 22⟩† @ Lean.Elab.Term.elabIdent
                                      • [Completion-Id] __do_lift✝ : some ?_uniq.503 @ ⟨359, 2⟩†-⟨359, 22⟩†
                                      • [Term] __do_lift✝ : TSyntax `term @ ⟨359, 2⟩†-⟨359, 22⟩†
  • [Term] numQuot (isBinder := true) : MacroM (TSyntax `term) @ ⟨357, 4⟩-⟨357, 11⟩
  • [Term] numQuot (isBinder := true) : MacroM (TSyntax `term) @ ⟨357, 4⟩-⟨357, 11⟩
-/
#guard_msgs in
#info_trees in
def numQuot : MacroM (TSyntax `term) := do
  let x : TSyntax `num := Syntax.mkNumLit "1"
  return (← `($x:num))

/--
info: • [Command] @ ⟨711, 0⟩-⟨713, 24⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] MacroM (TSyntax `term) : Type @ ⟨711, 16⟩-⟨711, 38⟩ @ Lean.Elab.Term.elabApp
    • [Completion-Id] MacroM : some Sort.{?_uniq.546} @ ⟨711, 16⟩-⟨711, 22⟩
    • [Term] MacroM : Type → Type @ ⟨711, 16⟩-⟨711, 22⟩
    • [Term] TSyntax `term : Type @ ⟨711, 23⟩-⟨711, 38⟩ @ Lean.Elab.Term.expandParen
      • [MacroExpansion]
        (TSyntax `term)
        ===>
        TSyntax `term
        • [Term] TSyntax `term : Type @ ⟨711, 24⟩-⟨711, 37⟩ @ Lean.Elab.Term.elabApp
          • [Completion-Id] TSyntax : some Type @ ⟨711, 24⟩-⟨711, 31⟩
          • [Term] TSyntax : SyntaxNodeKinds → Type @ ⟨711, 24⟩-⟨711, 31⟩
          • [Term] `term : Name @ ⟨711, 32⟩-⟨711, 37⟩ @ Lean.Elab.Term.elabQuotedName
          • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
  • [CustomInfo(Lean.Elab.Term.BodyInfo)]
    • [Term] let x := mkIdent `foo;
      do
      let __do_lift ←
        do
          let _ ← MonadRef.mkInfoFromRefPos
          let _ ← getCurrMacroScope
          let _ ← MonadQuotation.getContext
          pure { raw := x.raw }
      pure __do_lift : MacroM (TSyntax `term) @ ⟨711, 42⟩-⟨713, 24⟩ @ Lean.Elab.Term.elabDo
      • [Term] MacroM : Type → Type @ ⟨711, 42⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabSyntheticHole
      • [Term] TSyntax `term : Type @ ⟨711, 42⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabSyntheticHole
      • [MacroExpansion]
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        ===>
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        • [Term] let x := mkIdent `foo;
          do
          let __do_lift ←
            do
              let _ ← MonadRef.mkInfoFromRefPos
              let _ ← getCurrMacroScope
              let _ ← MonadQuotation.getContext
              pure { raw := x.raw }
          pure __do_lift : MacroM (TSyntax `term) @ ⟨712, 2⟩†-⟨712, 31⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
          • [Term] let x := mkIdent `foo;
            do
            let __do_lift ←
              do
                let _ ← MonadRef.mkInfoFromRefPos
                let _ ← getCurrMacroScope
                let _ ← MonadQuotation.getContext
                pure { raw := x.raw }
            pure __do_lift : MacroM (TSyntax `term) @ ⟨712, 2⟩-⟨712, 31⟩
            • [Term] let x := mkIdent `foo;
              do
              let __do_lift ←
                do
                  let _ ← MonadRef.mkInfoFromRefPos
                  let _ ← getCurrMacroScope
                  let _ ← MonadQuotation.getContext
                  pure { raw := x.raw }
              pure __do_lift : MacroM (TSyntax `term) @ ⟨712, 2⟩†-⟨712, 31⟩† @ Lean.Elab.Term.elabLetDecl
              • [Term] Ident : Type @ ⟨712, 10⟩-⟨712, 15⟩ @ Lean.Elab.Term.elabIdent
                • [Completion-Id] Ident : some Sort.{?_uniq.625} @ ⟨712, 10⟩-⟨712, 15⟩
                • [Term] Ident : Type @ ⟨712, 10⟩-⟨712, 15⟩
              • [Term] mkIdent `foo : Ident @ ⟨712, 19⟩-⟨712, 31⟩ @ Lean.Elab.Term.elabApp
                • [Completion-Id] mkIdent : some Lean.Syntax.Ident @ ⟨712, 19⟩-⟨712, 26⟩
                • [Term] mkIdent : Name → Ident @ ⟨712, 19⟩-⟨712, 26⟩
                • [Term] `foo : Name @ ⟨712, 27⟩-⟨712, 31⟩ @ Lean.Elab.Term.elabQuotedName
              • [Term] x (isBinder := true) : Ident @ ⟨712, 6⟩-⟨712, 7⟩
              • [Term] do
                  let __do_lift ←
                    do
                      let _ ← MonadRef.mkInfoFromRefPos
                      let _ ← getCurrMacroScope
                      let _ ← MonadQuotation.getContext
                      pure { raw := x.raw }
                  pure __do_lift : MacroM (TSyntax `term) @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
                • [Term] do
                    let __do_lift ←
                      do
                        let _ ← MonadRef.mkInfoFromRefPos
                        let _ ← getCurrMacroScope
                        let _ ← MonadQuotation.getContext
                        pure { raw := x.raw }
                    pure __do_lift : MacroM (TSyntax `term) @ ⟨713, 2⟩†-⟨713, 24⟩†
                  • [Term] do
                      let __do_lift ←
                        do
                          let _ ← MonadRef.mkInfoFromRefPos
                          let _ ← getCurrMacroScope
                          let _ ← MonadQuotation.getContext
                          pure { raw := x.raw }
                      pure __do_lift : MacroM (TSyntax `term) @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Bind.bind✝ : some Lean.MacroM (Lean.TSyntax (List.cons.{0} Lean.SyntaxNodeKind (Lean.Name.mkStr1 "term") (List.nil.{0} Lean.SyntaxNodeKind))) @ ⟨713, 2⟩†-⟨713, 24⟩†
                    • [Term] @bind : {m : Type → Type} →
                        [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨713, 2⟩†-⟨713, 24⟩†
                    • [Term] do
                        let _ ← MonadRef.mkInfoFromRefPos
                        let _ ← getCurrMacroScope
                        let _ ← MonadQuotation.getContext
                        pure
                            {
                              raw :=
                                x.raw } : MacroM
                        (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabTypeAscription
                      • [Term] MacroM (TSyntax `term) : Type @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabApp
                        • [Term] MacroM : Type → Type @ ⟨711, 42⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabSyntheticHole
                        • [Term] TSyntax `term : Type @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabHole
                      • [Term] do
                          let _ ← MonadRef.mkInfoFromRefPos
                          let _ ← getCurrMacroScope
                          let _ ← MonadQuotation.getContext
                          pure
                              {
                                raw :=
                                  x.raw } : MacroM
                          (TSyntax
                            `term) @ ⟨713, 12⟩-⟨713, 23⟩ @ Lean.Elab.Term.Quotation.elabQuot._@.Lean.Elab.Quotation.3282600398._hygCtx._hyg.3
                        • [MacroExpansion]
                          failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
                          ===>
                          Bind.bind✝ MonadRef.mkInfoFromRefPos✝
                            (fun info✝ =>
                              Bind.bind✝ getCurrMacroScope✝
                                (fun scp✝ =>
                                  Bind.bind✝ MonadQuotation.getContext✝
                                    (fun quotCtx✝ =>
                                      Pure.pure✝ (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x)))))
                          • [Term] do
                              let _ ← MonadRef.mkInfoFromRefPos
                              let _ ← getCurrMacroScope
                              let _ ← MonadQuotation.getContext
                              pure
                                  {
                                    raw :=
                                      x.raw } : MacroM (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabApp
                            • [Completion-Id] Bind.bind✝ : some ?_uniq.623 ?_uniq.671 @ ⟨713, 12⟩†-⟨713, 23⟩†
                            • [Term] @bind : {m : Type → Type} →
                                [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨713, 12⟩†-⟨713, 23⟩†
                            • [Term] MonadRef.mkInfoFromRefPos : MacroM
                                SourceInfo @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabIdent
                              • [Completion-Id] MonadRef.mkInfoFromRefPos✝ : some ?_uniq.674 ?_uniq.676 @ ⟨713, 12⟩†-⟨713, 23⟩†
                              • [Term] @MonadRef.mkInfoFromRefPos : {m : Type → Type} →
                                  [Monad m] → [MonadRef m] → m SourceInfo @ ⟨713, 12⟩†-⟨713, 23⟩†
                            • [Term] fun info => do
                                let _ ← getCurrMacroScope
                                let _ ← MonadQuotation.getContext
                                pure
                                    {
                                      raw :=
                                        x.raw } : SourceInfo →
                                MacroM (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.expandParen
                              • [MacroExpansion]
                                (fun info✝ =>
                                  Bind.bind✝ getCurrMacroScope✝
                                    (fun scp✝ =>
                                      Bind.bind✝ MonadQuotation.getContext✝
                                        (fun quotCtx✝ =>
                                          Pure.pure✝
                                            (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x)))))
                                ===>
                                fun info✝ =>
                                  Bind.bind✝ getCurrMacroScope✝
                                    (fun scp✝ =>
                                      Bind.bind✝ MonadQuotation.getContext✝
                                        (fun quotCtx✝ =>
                                          Pure.pure✝
                                            (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x))))
                                • [Term] fun info => do
                                    let _ ← getCurrMacroScope
                                    let _ ← MonadQuotation.getContext
                                    pure
                                        {
                                          raw :=
                                            x.raw } : SourceInfo →
                                    MacroM (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabFun
                                  • [Term] SourceInfo : Type @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabHole
                                  • [Term] info✝ (isBinder := true) : SourceInfo @ ⟨713, 12⟩†-⟨713, 23⟩†
                                  • [Term] do
                                      let _ ← getCurrMacroScope
                                      let _ ← MonadQuotation.getContext
                                      pure
                                          {
                                            raw :=
                                              x.raw } : MacroM
                                      (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabApp
                                    • [Completion-Id] Bind.bind✝ : some ?_uniq.674 ?_uniq.677 @ ⟨713, 12⟩†-⟨713, 23⟩†
                                    • [Term] @bind : {m : Type → Type} →
                                        [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨713, 12⟩†-⟨713, 23⟩†
                                    • [Term] getCurrMacroScope : MacroM
                                        MacroScope @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabIdent
                                      • [Completion-Id] getCurrMacroScope✝ : some ?_uniq.769 ?_uniq.771 @ ⟨713, 12⟩†-⟨713, 23⟩†
                                      • [Term] @getCurrMacroScope : {m : Type → Type} →
                                          [self : MonadQuotation m] → m MacroScope @ ⟨713, 12⟩†-⟨713, 23⟩†
                                    • [Term] fun scp => do
                                        let _ ← MonadQuotation.getContext
                                        pure
                                            {
                                              raw :=
                                                x.raw } : MacroScope →
                                        MacroM (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.expandParen
                                      • [MacroExpansion]
                                        (fun scp✝ =>
                                          Bind.bind✝ MonadQuotation.getContext✝
                                            (fun quotCtx✝ =>
                                              Pure.pure✝
                                                (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x))))
                                        ===>
                                        fun scp✝ =>
                                          Bind.bind✝ MonadQuotation.getContext✝
                                            (fun quotCtx✝ =>
                                              Pure.pure✝
                                                (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x)))
                                        • [Term] fun scp => do
                                            let _ ← MonadQuotation.getContext
                                            pure
                                                {
                                                  raw :=
                                                    x.raw } : MacroScope →
                                            MacroM (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabFun
                                          • [Term] MacroScope : Type @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabHole
                                          • [Term] scp✝ (isBinder := true) : MacroScope @ ⟨713, 12⟩†-⟨713, 23⟩†
                                          • [Term] do
                                              let _ ← MonadQuotation.getContext
                                              pure
                                                  {
                                                    raw :=
                                                      x.raw } : MacroM
                                              (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabApp
                                            • [Completion-Id] Bind.bind✝ : some ?_uniq.769 ?_uniq.772 @ ⟨713, 12⟩†-⟨713, 23⟩†
                                            • [Term] @bind : {m : Type → Type} →
                                                [self : Bind m] →
                                                  {α β : Type} → m α → (α → m β) → m β @ ⟨713, 12⟩†-⟨713, 23⟩†
                                            • [Term] MonadQuotation.getContext : MacroM
                                                Name @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabIdent
                                              • [Completion-Id] MonadQuotation.getContext✝ : some ?_uniq.819 ?_uniq.821 @ ⟨713, 12⟩†-⟨713, 23⟩†
                                              • [Term] @MonadQuotation.getContext : {m : Type → Type} →
                                                  [self : MonadQuotation m] → m Name @ ⟨713, 12⟩†-⟨713, 23⟩†
                                            • [Term] fun quotCtx =>
                                                pure
                                                  {
                                                    raw :=
                                                      x.raw } : Name →
                                                MacroM
                                                  (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.expandParen
                                              • [MacroExpansion]
                                                (fun quotCtx✝ =>
                                                  Pure.pure✝
                                                    (@TSyntax.mk✝ `term
                                                      (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x)))
                                                ===>
                                                fun quotCtx✝ =>
                                                  Pure.pure✝
                                                    (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x))
                                                • [Term] fun quotCtx =>
                                                    pure
                                                      {
                                                        raw :=
                                                          x.raw } : Name →
                                                    MacroM
                                                      (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabFun
                                                  • [Term] Name : Type @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabHole
                                                  • [Term] quotCtx✝ (isBinder := true) : Name @ ⟨713, 12⟩†-⟨713, 23⟩†
                                                  • [Term] pure
                                                      {
                                                        raw :=
                                                          x.raw } : MacroM
                                                      (TSyntax `term) @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabApp
                                                    • [Completion-Id] Pure.pure✝ : some ?_uniq.819 ?_uniq.822 @ ⟨713, 12⟩†-⟨713, 23⟩†
                                                    • [Term] @pure : {f : Type → Type} →
                                                        [self : Pure f] → {α : Type} → α → f α @ ⟨713, 12⟩†-⟨713, 23⟩†
                                                    • [Term] {
                                                        raw :=
                                                          x.raw } : TSyntax
                                                        `term @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.expandParen
                                                      • [MacroExpansion]
                                                        (@TSyntax.mk✝ `term
                                                          (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x))
                                                        ===>
                                                        @TSyntax.mk✝ `term
                                                          (@TSyntax.raw✝ (List.cons✝ `ident List.nil✝) x)
                                                        • [Term] {
                                                            raw :=
                                                              x.raw } : TSyntax
                                                            `term @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabApp
                                                          • [Completion-Id] TSyntax.mk✝ : some ?_uniq.870 @ ⟨713, 12⟩†-⟨713, 23⟩†
                                                          • [Term] @TSyntax.mk : {ks : SyntaxNodeKinds} →
                                                              Syntax → TSyntax ks @ ⟨713, 12⟩†-⟨713, 23⟩†
                                                          • [Term] `term : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                                                          • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
                                                          • [Term] x.raw : Syntax @ ⟨713, 12⟩†-⟨713, 23⟩† @ Lean.Elab.Term.elabApp
                                                            • [Completion-Id] TSyntax.raw✝ : some Lean.Syntax @ ⟨713, 12⟩†-⟨713, 23⟩†
                                                            • [Term] @TSyntax.raw : {ks : SyntaxNodeKinds} →
                                                                TSyntax ks → Syntax @ ⟨713, 12⟩†-⟨713, 23⟩†
                                                            • [Term] [`ident] : List
                                                                SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabApp
                                                              • [Completion-Id] List.cons✝ : some Lean.SyntaxNodeKinds @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                              • [Term] @List.cons : {α : Type} →
                                                                  α → List α → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                              • [Term] `ident : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                                                              • [Term] [] : List
                                                                  SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabIdent
                                                                • [Completion-Id] List.nil✝ : some List.{?_uniq.947} ?_uniq.948 @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                                • [Term] @List.nil : {α : Type} →
                                                                    List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                            • [Term] x : Ident @ ⟨713, 15⟩-⟨713, 16⟩ @ Lean.Elab.Term.elabIdent
                                                              • [Completion-Id] x : some Lean.TSyntax (List.cons.{?_uniq.947} ?_uniq.948 (Lean.Name.mkStr1 "ident") (List.nil.{?_uniq.949} ?_uniq.950)) @ ⟨713, 15⟩-⟨713, 16⟩
                                                              • [Term] x : Ident @ ⟨713, 15⟩-⟨713, 16⟩
                    • [Term] fun __do_lift =>
                        pure
                          __do_lift : TSyntax `term →
                        MacroM (TSyntax `term) @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.expandParen
                      • [MacroExpansion]
                        (fun (__do_lift✝ : _) =>
                          with_annotate_term(Term.doReturn
                               "return"
                               [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `__do_lift✝ ")")])
                            Pure.pure✝ (__do_lift✝))
                        ===>
                        fun (__do_lift✝ : _) =>
                          with_annotate_term(Term.doReturn
                               "return"
                               [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `__do_lift✝ ")")])
                            Pure.pure✝ (__do_lift✝)
                        • [Term] fun __do_lift =>
                            pure
                              __do_lift : TSyntax `term →
                            MacroM (TSyntax `term) @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabFun
                          • [Term] TSyntax `term : Type @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabHole
                          • [Term] __do_lift✝ (isBinder := true) : TSyntax `term @ ⟨713, 2⟩†-⟨713, 24⟩†
                          • [Term] pure
                              __do_lift✝ : MacroM
                              (TSyntax `term) @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
                            • [Term] pure __do_lift✝ : MacroM (TSyntax `term) @ ⟨713, 2⟩-⟨713, 24⟩
                              • [Term] pure
                                  __do_lift✝ : MacroM (TSyntax `term) @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabApp
                                • [Completion-Id] Pure.pure✝ : some ?_uniq.629 ?_uniq.632 @ ⟨713, 2⟩†-⟨713, 24⟩†
                                • [Term] @pure : {f : Type → Type} →
                                    [self : Pure f] → {α : Type} → α → f α @ ⟨713, 2⟩†-⟨713, 24⟩†
                                • [Term] __do_lift✝ : TSyntax `term @ ⟨713, 9⟩-⟨713, 24⟩ @ Lean.Elab.Term.expandParen
                                  • [MacroExpansion]
                                    (__do_lift✝)
                                    ===>
                                    __do_lift✝
                                    • [Term] __do_lift✝ : TSyntax
                                        `term @ ⟨713, 2⟩†-⟨713, 24⟩† @ Lean.Elab.Term.elabIdent
                                      • [Completion-Id] __do_lift✝ : some ?_uniq.992 @ ⟨713, 2⟩†-⟨713, 24⟩†
                                      • [Term] __do_lift✝ : TSyntax `term @ ⟨713, 2⟩†-⟨713, 24⟩†
  • [Term] identQuot (isBinder := true) : MacroM (TSyntax `term) @ ⟨711, 4⟩-⟨711, 13⟩
  • [Term] identQuot (isBinder := true) : MacroM (TSyntax `term) @ ⟨711, 4⟩-⟨711, 13⟩
-/
#guard_msgs in
#info_trees in
def identQuot : MacroM (TSyntax `term) := do
  let x : Ident := mkIdent `foo
  return (← `($x:ident))

/--
info: • [Command] @ ⟨1068, 0⟩-⟨1070, 22⟩ @ Lean.Elab.Command.elabDeclaration
  • [Term] MacroM (TSyntax `term) : Type @ ⟨1068, 14⟩-⟨1068, 36⟩ @ Lean.Elab.Term.elabApp
    • [Completion-Id] MacroM : some Sort.{?_uniq.1035} @ ⟨1068, 14⟩-⟨1068, 20⟩
    • [Term] MacroM : Type → Type @ ⟨1068, 14⟩-⟨1068, 20⟩
    • [Term] TSyntax `term : Type @ ⟨1068, 21⟩-⟨1068, 36⟩ @ Lean.Elab.Term.expandParen
      • [MacroExpansion]
        (TSyntax `term)
        ===>
        TSyntax `term
        • [Term] TSyntax `term : Type @ ⟨1068, 22⟩-⟨1068, 35⟩ @ Lean.Elab.Term.elabApp
          • [Completion-Id] TSyntax : some Type @ ⟨1068, 22⟩-⟨1068, 29⟩
          • [Term] TSyntax : SyntaxNodeKinds → Type @ ⟨1068, 22⟩-⟨1068, 29⟩
          • [Term] `term : Name @ ⟨1068, 30⟩-⟨1068, 35⟩ @ Lean.Elab.Term.elabQuotedName
          • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
  • [CustomInfo(Lean.Elab.Term.BodyInfo)]
    • [Term] let x := Syntax.mkStrLit "hi";
      do
      let __do_lift ←
        do
          let _ ← MonadRef.mkInfoFromRefPos
          let _ ← getCurrMacroScope
          let _ ← MonadQuotation.getContext
          pure { raw := x.raw }
      pure __do_lift : MacroM (TSyntax `term) @ ⟨1068, 40⟩-⟨1070, 22⟩ @ Lean.Elab.Term.elabDo
      • [Term] MacroM : Type → Type @ ⟨1068, 40⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabSyntheticHole
      • [Term] TSyntax `term : Type @ ⟨1068, 40⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabSyntheticHole
      • [MacroExpansion]
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        ===>
        failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
        • [Term] let x := Syntax.mkStrLit "hi";
          do
          let __do_lift ←
            do
              let _ ← MonadRef.mkInfoFromRefPos
              let _ ← getCurrMacroScope
              let _ ← MonadQuotation.getContext
              pure { raw := x.raw }
          pure __do_lift : MacroM (TSyntax `term) @ ⟨1069, 2⟩†-⟨1069, 46⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
          • [Term] let x := Syntax.mkStrLit "hi";
            do
            let __do_lift ←
              do
                let _ ← MonadRef.mkInfoFromRefPos
                let _ ← getCurrMacroScope
                let _ ← MonadQuotation.getContext
                pure { raw := x.raw }
            pure __do_lift : MacroM (TSyntax `term) @ ⟨1069, 2⟩-⟨1069, 46⟩
            • [Term] let x := Syntax.mkStrLit "hi";
              do
              let __do_lift ←
                do
                  let _ ← MonadRef.mkInfoFromRefPos
                  let _ ← getCurrMacroScope
                  let _ ← MonadQuotation.getContext
                  pure { raw := x.raw }
              pure __do_lift : MacroM (TSyntax `term) @ ⟨1069, 2⟩†-⟨1069, 46⟩† @ Lean.Elab.Term.elabLetDecl
              • [Term] TSyntax `str : Type @ ⟨1069, 10⟩-⟨1069, 22⟩ @ Lean.Elab.Term.elabApp
                • [Completion-Id] TSyntax : some Sort.{?_uniq.1114} @ ⟨1069, 10⟩-⟨1069, 17⟩
                • [Term] TSyntax : SyntaxNodeKinds → Type @ ⟨1069, 10⟩-⟨1069, 17⟩
                • [Term] `str : Name @ ⟨1069, 18⟩-⟨1069, 22⟩ @ Lean.Elab.Term.elabQuotedName
                • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
              • [Term] Syntax.mkStrLit "hi" : StrLit @ ⟨1069, 26⟩-⟨1069, 46⟩ @ Lean.Elab.Term.elabApp
                • [Completion-Id] Syntax.mkStrLit : some Lean.TSyntax (List.cons.{0} Lean.SyntaxNodeKind (Lean.Name.mkStr1 "str") (List.nil.{0} Lean.SyntaxNodeKind)) @ ⟨1069, 26⟩-⟨1069, 41⟩
                • [Term] @Syntax.mkStrLit : String →
                    optParam SourceInfo SourceInfo.none → StrLit @ ⟨1069, 26⟩-⟨1069, 41⟩
                • [Term] "hi" : String @ ⟨1069, 42⟩-⟨1069, 46⟩ @ Lean.Elab.Term.elabStrLit
              • [Term] x (isBinder := true) : TSyntax `str @ ⟨1069, 6⟩-⟨1069, 7⟩
              • [Term] do
                  let __do_lift ←
                    do
                      let _ ← MonadRef.mkInfoFromRefPos
                      let _ ← getCurrMacroScope
                      let _ ← MonadQuotation.getContext
                      pure { raw := x.raw }
                  pure __do_lift : MacroM (TSyntax `term) @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
                • [Term] do
                    let __do_lift ←
                      do
                        let _ ← MonadRef.mkInfoFromRefPos
                        let _ ← getCurrMacroScope
                        let _ ← MonadQuotation.getContext
                        pure { raw := x.raw }
                    pure __do_lift : MacroM (TSyntax `term) @ ⟨1070, 2⟩†-⟨1070, 22⟩†
                  • [Term] do
                      let __do_lift ←
                        do
                          let _ ← MonadRef.mkInfoFromRefPos
                          let _ ← getCurrMacroScope
                          let _ ← MonadQuotation.getContext
                          pure { raw := x.raw }
                      pure __do_lift : MacroM (TSyntax `term) @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabApp
                    • [Completion-Id] Bind.bind✝ : some Lean.MacroM (Lean.TSyntax (List.cons.{0} Lean.SyntaxNodeKind (Lean.Name.mkStr1 "term") (List.nil.{0} Lean.SyntaxNodeKind))) @ ⟨1070, 2⟩†-⟨1070, 22⟩†
                    • [Term] @bind : {m : Type → Type} →
                        [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨1070, 2⟩†-⟨1070, 22⟩†
                    • [Term] do
                        let _ ← MonadRef.mkInfoFromRefPos
                        let _ ← getCurrMacroScope
                        let _ ← MonadQuotation.getContext
                        pure
                            {
                              raw :=
                                x.raw } : MacroM
                        (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabTypeAscription
                      • [Term] MacroM (TSyntax `term) : Type @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabApp
                        • [Term] MacroM : Type → Type @ ⟨1068, 40⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabSyntheticHole
                        • [Term] TSyntax `term : Type @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabHole
                      • [Term] do
                          let _ ← MonadRef.mkInfoFromRefPos
                          let _ ← getCurrMacroScope
                          let _ ← MonadQuotation.getContext
                          pure
                              {
                                raw :=
                                  x.raw } : MacroM
                          (TSyntax
                            `term) @ ⟨1070, 12⟩-⟨1070, 21⟩ @ Lean.Elab.Term.Quotation.elabQuot._@.Lean.Elab.Quotation.3282600398._hygCtx._hyg.3
                        • [MacroExpansion]
                          failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
                          ===>
                          Bind.bind✝ MonadRef.mkInfoFromRefPos✝
                            (fun info✝ =>
                              Bind.bind✝ getCurrMacroScope✝
                                (fun scp✝ =>
                                  Bind.bind✝ MonadQuotation.getContext✝
                                    (fun quotCtx✝ =>
                                      Pure.pure✝ (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x)))))
                          • [Term] do
                              let _ ← MonadRef.mkInfoFromRefPos
                              let _ ← getCurrMacroScope
                              let _ ← MonadQuotation.getContext
                              pure
                                  {
                                    raw :=
                                      x.raw } : MacroM
                              (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabApp
                            • [Completion-Id] Bind.bind✝ : some ?_uniq.1112 ?_uniq.1216 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                            • [Term] @bind : {m : Type → Type} →
                                [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                            • [Term] MonadRef.mkInfoFromRefPos : MacroM
                                SourceInfo @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabIdent
                              • [Completion-Id] MonadRef.mkInfoFromRefPos✝ : some ?_uniq.1219 ?_uniq.1221 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                              • [Term] @MonadRef.mkInfoFromRefPos : {m : Type → Type} →
                                  [Monad m] → [MonadRef m] → m SourceInfo @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                            • [Term] fun info => do
                                let _ ← getCurrMacroScope
                                let _ ← MonadQuotation.getContext
                                pure
                                    {
                                      raw :=
                                        x.raw } : SourceInfo →
                                MacroM (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.expandParen
                              • [MacroExpansion]
                                (fun info✝ =>
                                  Bind.bind✝ getCurrMacroScope✝
                                    (fun scp✝ =>
                                      Bind.bind✝ MonadQuotation.getContext✝
                                        (fun quotCtx✝ =>
                                          Pure.pure✝
                                            (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x)))))
                                ===>
                                fun info✝ =>
                                  Bind.bind✝ getCurrMacroScope✝
                                    (fun scp✝ =>
                                      Bind.bind✝ MonadQuotation.getContext✝
                                        (fun quotCtx✝ =>
                                          Pure.pure✝
                                            (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x))))
                                • [Term] fun info => do
                                    let _ ← getCurrMacroScope
                                    let _ ← MonadQuotation.getContext
                                    pure
                                        {
                                          raw :=
                                            x.raw } : SourceInfo →
                                    MacroM (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabFun
                                  • [Term] SourceInfo : Type @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabHole
                                  • [Term] info✝ (isBinder := true) : SourceInfo @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                  • [Term] do
                                      let _ ← getCurrMacroScope
                                      let _ ← MonadQuotation.getContext
                                      pure
                                          {
                                            raw :=
                                              x.raw } : MacroM
                                      (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabApp
                                    • [Completion-Id] Bind.bind✝ : some ?_uniq.1219 ?_uniq.1222 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                    • [Term] @bind : {m : Type → Type} →
                                        [self : Bind m] → {α β : Type} → m α → (α → m β) → m β @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                    • [Term] getCurrMacroScope : MacroM
                                        MacroScope @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabIdent
                                      • [Completion-Id] getCurrMacroScope✝ : some ?_uniq.1314 ?_uniq.1316 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                      • [Term] @getCurrMacroScope : {m : Type → Type} →
                                          [self : MonadQuotation m] → m MacroScope @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                    • [Term] fun scp => do
                                        let _ ← MonadQuotation.getContext
                                        pure
                                            {
                                              raw :=
                                                x.raw } : MacroScope →
                                        MacroM (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.expandParen
                                      • [MacroExpansion]
                                        (fun scp✝ =>
                                          Bind.bind✝ MonadQuotation.getContext✝
                                            (fun quotCtx✝ =>
                                              Pure.pure✝
                                                (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x))))
                                        ===>
                                        fun scp✝ =>
                                          Bind.bind✝ MonadQuotation.getContext✝
                                            (fun quotCtx✝ =>
                                              Pure.pure✝
                                                (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x)))
                                        • [Term] fun scp => do
                                            let _ ← MonadQuotation.getContext
                                            pure
                                                {
                                                  raw :=
                                                    x.raw } : MacroScope →
                                            MacroM (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabFun
                                          • [Term] MacroScope : Type @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabHole
                                          • [Term] scp✝ (isBinder := true) : MacroScope @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                          • [Term] do
                                              let _ ← MonadQuotation.getContext
                                              pure
                                                  {
                                                    raw :=
                                                      x.raw } : MacroM
                                              (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabApp
                                            • [Completion-Id] Bind.bind✝ : some ?_uniq.1314 ?_uniq.1317 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                            • [Term] @bind : {m : Type → Type} →
                                                [self : Bind m] →
                                                  {α β : Type} → m α → (α → m β) → m β @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                            • [Term] MonadQuotation.getContext : MacroM
                                                Name @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabIdent
                                              • [Completion-Id] MonadQuotation.getContext✝ : some ?_uniq.1364 ?_uniq.1366 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                              • [Term] @MonadQuotation.getContext : {m : Type → Type} →
                                                  [self : MonadQuotation m] → m Name @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                            • [Term] fun quotCtx =>
                                                pure
                                                  {
                                                    raw :=
                                                      x.raw } : Name →
                                                MacroM
                                                  (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.expandParen
                                              • [MacroExpansion]
                                                (fun quotCtx✝ =>
                                                  Pure.pure✝
                                                    (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x)))
                                                ===>
                                                fun quotCtx✝ =>
                                                  Pure.pure✝
                                                    (@TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x))
                                                • [Term] fun quotCtx =>
                                                    pure
                                                      {
                                                        raw :=
                                                          x.raw } : Name →
                                                    MacroM
                                                      (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabFun
                                                  • [Term] Name : Type @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabHole
                                                  • [Term] quotCtx✝ (isBinder := true) : Name @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                                  • [Term] pure
                                                      {
                                                        raw :=
                                                          x.raw } : MacroM
                                                      (TSyntax `term) @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabApp
                                                    • [Completion-Id] Pure.pure✝ : some ?_uniq.1364 ?_uniq.1367 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                                    • [Term] @pure : {f : Type → Type} →
                                                        [self : Pure f] → {α : Type} → α → f α @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                                    • [Term] {
                                                        raw :=
                                                          x.raw } : TSyntax
                                                        `term @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.expandParen
                                                      • [MacroExpansion]
                                                        (@TSyntax.mk✝ `term
                                                          (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x))
                                                        ===>
                                                        @TSyntax.mk✝ `term (@TSyntax.raw✝ (List.cons✝ `str List.nil✝) x)
                                                        • [Term] {
                                                            raw :=
                                                              x.raw } : TSyntax
                                                            `term @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabApp
                                                          • [Completion-Id] TSyntax.mk✝ : some ?_uniq.1415 @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                                          • [Term] @TSyntax.mk : {ks : SyntaxNodeKinds} →
                                                              Syntax → TSyntax ks @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                                          • [Term] `term : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                                                          • [CustomInfo(Lean.Elab.Term.CoeExpansionTrace)]
                                                          • [Term] x.raw : Syntax @ ⟨1070, 12⟩†-⟨1070, 21⟩† @ Lean.Elab.Term.elabApp
                                                            • [Completion-Id] TSyntax.raw✝ : some Lean.Syntax @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                                            • [Term] @TSyntax.raw : {ks : SyntaxNodeKinds} →
                                                                TSyntax ks → Syntax @ ⟨1070, 12⟩†-⟨1070, 21⟩†
                                                            • [Term] [`str] : List
                                                                SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabApp
                                                              • [Completion-Id] List.cons✝ : some Lean.SyntaxNodeKinds @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                              • [Term] @List.cons : {α : Type} →
                                                                  α → List α → List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                              • [Term] `str : Name @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabQuotedName
                                                              • [Term] [] : List
                                                                  SyntaxNodeKind @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Term.elabIdent
                                                                • [Completion-Id] List.nil✝ : some List.{?_uniq.1492} ?_uniq.1493 @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                                • [Term] @List.nil : {α : Type} →
                                                                    List α @ ⟨1, 0⟩†-⟨1, 0⟩†
                                                            • [Term] x : TSyntax
                                                                `str @ ⟨1070, 15⟩-⟨1070, 16⟩ @ Lean.Elab.Term.elabIdent
                                                              • [Completion-Id] x : some Lean.TSyntax (List.cons.{?_uniq.1492} ?_uniq.1493 (Lean.Name.mkStr1 "str") (List.nil.{?_uniq.1494} ?_uniq.1495)) @ ⟨1070, 15⟩-⟨1070, 16⟩
                                                              • [Term] x : TSyntax `str @ ⟨1070, 15⟩-⟨1070, 16⟩
                    • [Term] fun __do_lift =>
                        pure
                          __do_lift : TSyntax `term →
                        MacroM (TSyntax `term) @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.expandParen
                      • [MacroExpansion]
                        (fun (__do_lift✝ : _) =>
                          with_annotate_term(Term.doReturn
                               "return"
                               [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `__do_lift✝ ")")])
                            Pure.pure✝ (__do_lift✝))
                        ===>
                        fun (__do_lift✝ : _) =>
                          with_annotate_term(Term.doReturn
                               "return"
                               [(Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) `__do_lift✝ ")")])
                            Pure.pure✝ (__do_lift✝)
                        • [Term] fun __do_lift =>
                            pure
                              __do_lift : TSyntax `term →
                            MacroM (TSyntax `term) @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabFun
                          • [Term] TSyntax `term : Type @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabHole
                          • [Term] __do_lift✝ (isBinder := true) : TSyntax `term @ ⟨1070, 2⟩†-⟨1070, 22⟩†
                          • [Term] pure
                              __do_lift✝ : MacroM
                              (TSyntax `term) @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabWithAnnotateTerm
                            • [Term] pure __do_lift✝ : MacroM (TSyntax `term) @ ⟨1070, 2⟩-⟨1070, 22⟩
                              • [Term] pure
                                  __do_lift✝ : MacroM (TSyntax `term) @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabApp
                                • [Completion-Id] Pure.pure✝ : some ?_uniq.1174 ?_uniq.1177 @ ⟨1070, 2⟩†-⟨1070, 22⟩†
                                • [Term] @pure : {f : Type → Type} →
                                    [self : Pure f] → {α : Type} → α → f α @ ⟨1070, 2⟩†-⟨1070, 22⟩†
                                • [Term] __do_lift✝ : TSyntax `term @ ⟨1070, 9⟩-⟨1070, 22⟩ @ Lean.Elab.Term.expandParen
                                  • [MacroExpansion]
                                    (__do_lift✝)
                                    ===>
                                    __do_lift✝
                                    • [Term] __do_lift✝ : TSyntax
                                        `term @ ⟨1070, 2⟩†-⟨1070, 22⟩† @ Lean.Elab.Term.elabIdent
                                      • [Completion-Id] __do_lift✝ : some ?_uniq.1537 @ ⟨1070, 2⟩†-⟨1070, 22⟩†
                                      • [Term] __do_lift✝ : TSyntax `term @ ⟨1070, 2⟩†-⟨1070, 22⟩†
  • [Term] strQuot (isBinder := true) : MacroM (TSyntax `term) @ ⟨1068, 4⟩-⟨1068, 11⟩
  • [Term] strQuot (isBinder := true) : MacroM (TSyntax `term) @ ⟨1068, 4⟩-⟨1068, 11⟩
-/
#guard_msgs in
#info_trees in
def strQuot : MacroM (TSyntax `term) := do
  let x : TSyntax `str := Syntax.mkStrLit "hi"
  return (← `($x:str))

example (id : Lean.Syntax.Ident) : Lean.Name := id.
                                                 --^ textDocument/completion
example (id : Lean.TSyntax `ident) : Lean.Name := id.
                                                   --^ textDocument/completion

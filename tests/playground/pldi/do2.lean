open Lean

/-
inductive Syntax
| missing : Syntax
| node   (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax
| atom   (info : SourceInfo) (val : String) : Syntax
| ident  (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : List (Name × List String)) : Syntax
-/

partial def expandHash : Syntax → StateT Bool MacroM Syntax
| Syntax.node k args =>
  if k == `doHash then do set true; `(←MonadState.get)
  else do
    args ← args.mapM expandHash;
    pure $ Syntax.node k args
| stx => pure stx

@[macro Lean.Parser.Term.do] def expandDo : Macro :=
fun stx => do
  (stx, expanded) ← expandHash stx false;
  if expanded then pure stx
  else Macro.throwUnsupported



syntax:max [doHash] "#" : term

def tst : StateT (Nat × Nat) IO Unit := do
if #.1 == 0 then
  IO.println "first field is zero"
else
  IO.println "first field is not zero"

#eval tst.run' (1, 1)
#eval tst.run' (0, 1)

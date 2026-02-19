import Lean
open Lean

set_option guard_msgs.diff false

#info_trees in
def miscQuot : MacroM (TSyntax `term) := do
  let numStx : TSyntax `num := Syntax.mkNumLit "1"
  let identStx : TSyntax `ident := mkIdent `foo
  let strStx : TSyntax `str := Syntax.mkStrLit "hi"
  let charStx : TSyntax `char := Syntax.mkCharLit 'A'
  let sciStx : TSyntax `scientific := Syntax.mkScientificLit "1.2e3"
  let nameStx : TSyntax `name := Syntax.mkNameLit "`Foo"
  let fieldStx : TSyntax `fieldIdx := Syntax.mkLit fieldIdxKind "2"
  let hygieneStx : TSyntax `hygieneInfo :=
    ⟨Syntax.node SourceInfo.none hygieneInfoKind #[mkIdent `x]⟩
  let lit1 : Syntax := Syntax.mkLit interpolatedStrLitKind "foo{"
  let lit2 : Syntax := Syntax.mkLit interpolatedStrLitKind "}"
  let interp : TSyntax `interpolatedStrKind :=
    ⟨Syntax.node SourceInfo.none interpolatedStrKind #[lit1, Syntax.mkNumLit "1", lit2]⟩
  let hexStx : TSyntax `hexnum := Syntax.mkLit hexnumKind "ea10"
  let e : TSyntax `term := mkIdent `x
  let _ ← `($numStx:num)
  let _ ← `($identStx:ident)
  let _ ← `($strStx:str)
  let _ ← `($charStx:char)
  let _ ← `($sciStx:scientific)
  let _ ← `($nameStx:name)
  let _ ← `($e.$fieldStx:fieldIdx)
  let _ ← `(($hygieneStx:hygieneInfo $e))
  let _ ← `(throwError $interp:interpolatedStr)
  let _ ← `(Parser.Tactic.grindParam| #$hexStx:hexnum)
  return (← `($e))

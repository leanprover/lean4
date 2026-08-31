import Lean

open Lean Meta

def test := 1

-- These should produce different auxiliary names:
-- (e.g. by including the declaration name)
-- it used to be `info: _kind_1` in both cases, without the prefix

/--
info: test.foo1._kind_1
---
info: test.foo2._kind_1
-/
#guard_msgs in
#eval do
  realizeConst `test `test.foo1 do
    let n ← mkAuxDeclName (kind := `_kind)
    logInfo n
    addDecl (.thmDecl {name := `test.foo1, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro})
  realizeConst `test `test.foo2 do
    let n ← mkAuxDeclName (kind := `_kind)
    logInfo n
    addDecl (.thmDecl {name := `test.foo2, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro})

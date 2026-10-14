import AttrTest.Ext

/-! The attribute is defined here, alongside its applications. -/

open Lean

@[attribute] def markAttr : AttributeImpl where
  name := `mark
  descr := "mark a declaration into markedExt"
  add := fun decl _stx _kind => do
    modifyEnv fun env => markedExt.addEntry env decl

@[mark] def foo := 1
@[mark] def bar := 2
@[mark] def baz := 3

/-- info: [foo, bar, baz] -/
#guard_msgs in
run_meta Lean.logInfo m!"{getMarked (← Lean.getEnv)}"

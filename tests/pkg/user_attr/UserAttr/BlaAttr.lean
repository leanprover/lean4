module

public import Lean

open Lean

public meta initialize blaAttr : TagAttribute ← registerTagAttribute `bla "simple user defined attribute"

/-- My own new simp attribute. -/
register_simp_attr my_simp

syntax (name := foo) "foo" num "important"? : attr

public meta initialize fooAttr : ParametricAttribute (Nat × Bool) ←
  registerParametricAttribute {
    name := `foo
    descr := "parametric attribute containing a priority and flag"
    getParam := fun _ stx =>
      match stx with
      | `(attr| foo $prio:num $[important%$imp]?) =>
        return (prio.getNat, imp.isSome)
      | _  => throwError "unexpected foo attribute"
    afterSet := fun declName _ => do
      IO.println s!"set attribute [foo] at {declName}"
  }

syntax (name := trace_add) "trace_add" : attr

public meta initialize registerBuiltinAttribute {
  name := `trace_add
  descr := "Simply traces when added, to debug double-application bugs"
  add   := fun decl _stx _kind => do
    logInfo m!"trace_add attribute added to {decl}"
  -- applicationTime := .afterCompilation
}

syntax (name := myattr_beforeElaboration) "myattr_beforeElaboration" : attr
public meta initialize registerBuiltinAttribute {
  name := `myattr_beforeElaboration
  descr := "Simply traces when added, to debug application bugs"
  add decl _ _ := do
    let c := if (← getEnv).contains decl then m!"already in environment" else m!"not in environment"
    logInfo m!"declaration `{decl}` tagged `myattr_beforeElaboration`, {c}"
  applicationTime := .beforeElaboration
}
syntax (name := myattr_afterTypeChecking) "myattr_afterTypeChecking" : attr
public meta initialize registerBuiltinAttribute {
  name := `myattr_afterTypeChecking
  descr := "Simply traces when added, to debug application bugs"
  add decl _ _ := do
    let c := if (← getEnv).contains decl then m!"already in environment" else m!"not in environment"
    logInfo m!"declaration `{decl}` tagged `myattr_afterTypeChecking`, {c}"
  applicationTime := .afterTypeChecking
}
syntax (name := myattr_afterCompilation) "myattr_afterCompilation" : attr
public meta initialize registerBuiltinAttribute {
  name := `myattr_afterCompilation
  descr := "Simply traces when added, to debug application bugs"
  add decl _ _ := do
    let c := if (← getEnv).contains decl then m!"already in environment" else m!"not in environment"
    logInfo m!"declaration `{decl}` tagged `myattr_afterCompilation`, {c}"
  applicationTime := .afterCompilation
}

register_grind_attr my_grind

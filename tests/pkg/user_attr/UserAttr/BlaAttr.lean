import Lean

open Lean

initialize blaAttr : TagAttribute ← registerTagAttribute `bla "simple user defined attribute"

/-- My own new simp attribute. -/
register_simp_attr my_simp

syntax (name := foo) "foo" num "important"? : attr

initialize fooAttr : ParametricAttribute (Nat × Bool) ←
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

initialize registerBuiltinAttribute {
  name := `trace_add
  descr := "Simply traces when added, to debug double-application bugs"
  add   := fun decl _stx _kind => do
    logInfo m!"trace_add attribute added to {decl}"
  -- applicationTime := .afterCompilation
}

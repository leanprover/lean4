import Lean

open Lean

initialize blaAttr : TagAttribute ← registerTagAttribute `bla "simple user defined attribute"

/-- My new simp attribute -/
register_simp_attr my_simp "my own simp attribute"

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

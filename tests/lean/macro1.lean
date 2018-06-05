import init.lean.parser.macro
attribute [instance] lean.name.has_lt_quick
namespace lean
open lean.parser

def sp : option span := none

def lambda_macro := {macro .
  name := "lambda",
  expand := some $ λ node,
  match node.args with
  | [ident@(syntax.ident _), body] :=
     syntax.node {macro := `lambda_core, span := sp, args := [
       syntax.node {macro := `bind, span := sp, args := [
         syntax.lst [ident],
         body
       ]}
     ]}
  | _ := syntax.node node}

def intro_x_macro := {macro .
  name := "intro_x",
  expand := some $ λ node,
    syntax.node ⟨sp, "lambda", syntax.ident ⟨sp, "x", none, none⟩ :: node.args⟩}

def macros : name → option macro
| `lambda := some lambda_macro
| `intro_x := some intro_x_macro
| _ := none

def cfg : parse_state :=
{macros := rbmap.from_list ([lambda_macro, intro_x_macro].map (λ m, (m.name, m))) _,
 resolve_cfg := {global_scope := mk_rbmap _ _ _}}

meta def test (stx : syntax) : command :=
match (expand' stx >>= resolve').run' cfg () with
| except.error e := tactic.fail e
| except.ok stx  := tactic.trace stx

run_cmd test $ syntax.node ⟨sp, "lambda", [
  syntax.ident ⟨sp, "x", none, none⟩,
  syntax.ident ⟨sp, "x", none, none⟩
]⟩

run_cmd test $ syntax.node ⟨sp, "lambda", [
  syntax.ident ⟨sp, "x", none, none⟩,
  syntax.ident ⟨sp, "y", none, none⟩
]⟩

-- test macro shadowing
run_cmd test $ syntax.node ⟨sp, "lambda", [
  syntax.ident ⟨sp, "x", none, none⟩,
  syntax.node ⟨sp, "intro_x", [
    syntax.ident ⟨sp, "x", none, none⟩
  ]⟩
]⟩

-- test field notation
run_cmd test $ syntax.node ⟨sp, "lambda", [
  syntax.ident ⟨sp, `x.y, none, none⟩,
  syntax.ident ⟨sp, `x.y.z, none, none⟩
]⟩

end lean

import init.lean.parser.macro
attribute [instance] lean.name.has_lt_quick
namespace macro1
open lean.parser

def info : option source_info := none

def lambda_macro := {macro .
  name := `lambda,
  expand := some $ λ node,
  match node.args with
  | [syntax.node ⟨name.anonymous, [ident@(syntax.ident _)]⟩, body] :=
     syntax.node {macro := `lambda_core, args := [
       syntax.node {macro := `bind, args := [
         syntax.node {macro := name.anonymous, args := [ident]},
         body
       ]}
     ]}
  | [syntax.node ⟨name.anonymous, id::ids⟩, body] :=
    syntax.node ⟨`lambda, [syntax.node ⟨name.anonymous, [id]⟩,
                           syntax.node ⟨`lambda, [syntax.node ⟨name.anonymous, ids⟩,
                                                  body]⟩]⟩
  | _ := none}

def intro_x_macro := {macro .
  name := "intro_x",
  expand := some $ λ node,
    syntax.node ⟨`lambda, syntax.node ⟨name.anonymous, [syntax.ident ⟨info, "x", none, none⟩]⟩ :: node.args⟩}

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

#eval test $ syntax.node ⟨`lambda, [
  syntax.node ⟨name.anonymous, [syntax.ident ⟨info, `x, none, none⟩]⟩,
  syntax.ident ⟨info, `x, none, none⟩
]⟩

#eval test $ syntax.node ⟨`lambda, [
  syntax.node ⟨name.anonymous, [syntax.ident ⟨info, `x, none, none⟩]⟩,
  syntax.ident ⟨info, `y, none, none⟩
]⟩

-- test macro shadowing
#eval test $ syntax.node ⟨`lambda, [
  syntax.node ⟨name.anonymous, [syntax.ident ⟨info, `x, none, none⟩]⟩,
  syntax.node ⟨`intro_x, [
    syntax.ident ⟨info, `x, none, none⟩
  ]⟩
]⟩

-- test field notation
#eval test $ syntax.node ⟨`lambda, [
  syntax.node ⟨name.anonymous, [syntax.ident ⟨info, `x.y, none, none⟩]⟩,
  syntax.ident ⟨info, `x.y.z, none, none⟩
]⟩

end macro1

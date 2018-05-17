import init.lean.parser.macro

meta def name.to_lean_name : name → lean.name
| name.anonymous := lean.name.anonymous
| (name.mk_string s n) := n.to_lean_name.mk_string s
| (name.mk_numeral u n) := n.to_lean_name.mk_numeral u.to_nat

meta instance : has_coe name lean.name :=
⟨name.to_lean_name⟩

namespace lean
open lean.parser

def sp : option span := none

def lambda_macro := {macro .
  name := "lambda",
  resolve := some $ λ sc node,
  do [syntax.ident ident, body] ← pure node.args
       | throw "unreachable",
     pure [sc, sc.insert (ident.name, ident.msc) ident.id]}

def resolve_name (msc : option macro_scope_id) (sc : scope) : name → option resolved
| (name.mk_string n s) :=
do {
  decl ← sc.find (n.mk_string s, msc),
  pure ⟨sum.inl decl, n.mk_string s⟩
} <|> resolve_name n
| _ := none

def ref_macro := {macro .
  name := "ref",
  resolve := some $ λ sc node,
  do [syntax.ident ident] ← pure node.args
       | throw "unreachable",
     some resolved ← pure $ resolve_name ident.msc sc ident.name
       | throw sformat!"unknown identifier {ident.name}",
     modify (λ st, ⟨st.resolve_map.insert ident.id resolved⟩),
     pure []}

def intro_x_macro := {macro .
  name := "intro_x",
  expand := some $ λ node,
    -- TODO: how to manage IDs?
    syntax.node ⟨5, sp, "lambda", syntax.ident ⟨6, sp, "x", none⟩ :: node.args⟩}

def macros : name → option macro
| "lambda" := some lambda_macro
| "ref" := some ref_macro
| "intro_x" := some intro_x_macro
| _ := none

def cfg : parse_state :=
{macros := rbmap.from_list ([lambda_macro, ref_macro, intro_x_macro].map (λ m, (m.name, m))) _,
 resolve_cfg := {global_scope := mk_rbmap _ _ _}}

meta def format.to_root_format : format → _root_.format
| (format.nil) := _root_.format.nil
| (format.line) := _root_.format.line
| (format.text s) := s
| (format.nest n f) := f.to_root_format.nest n
| (format.compose ff f₁ f₂) := _root_.format.compose f₁.to_root_format f₂.to_root_format
| (format.compose tt f₁ f₂) := (_root_.format.compose f₁.to_root_format f₂.to_root_format).group
| (format.choice f₁ f₂) := f₁.to_root_format -- :/

meta instance has_lean_format_to_format {α} [has_to_format α] : _root_.has_to_format α :=
⟨format.to_root_format ∘ to_fmt⟩

namespace rbmap
  universes u v w
  variables {α : Type u} {β : Type v} {δ : Type w} {lt : α → α → Prop}
  open lean.format prod
  variables [has_to_format α] [has_to_format β]

  private meta def format_key_data (a : α) (b : β) (first : bool) : format :=
  (if first then to_fmt "" else to_fmt "," ++ to_fmt line) ++ to_fmt a ++ " " ++ to_fmt "←" ++ " " ++ to_fmt b

  private meta def to_format (m : rbmap α β lt) : format :=
  group $ to_fmt "⟨" ++ nest 1 (fst (rbmap.fold (λ a b p, (fst p ++ format_key_data a b (snd p), ff)) m (to_fmt "", tt))) ++
          to_fmt "⟩"

  meta instance : has_to_format (rbmap α β lt) :=
  ⟨to_format⟩
end rbmap

meta def test (stx : syntax) : command :=
match (expand' stx >>= resolve').run' cfg () with
| except.error e := tactic.fail e
| except.ok    (stx, ⟨rsm⟩) := tactic.trace stx >> tactic.trace (stx, rsm)

run_cmd test $ syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, "x", none⟩,
  syntax.node ⟨2, sp, "ref", [
    syntax.ident ⟨3, sp, "x", none⟩
  ]⟩
]⟩

-- test macro shadowing
run_cmd test $ syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, "x", none⟩,
  syntax.node ⟨4, sp, "intro_x", [
    syntax.node ⟨2, sp, "ref", [
      syntax.ident ⟨3, sp, "x", none⟩
    ]⟩
  ]⟩
]⟩

-- test field notation
run_cmd test $ syntax.node ⟨0, sp, "lambda", [
  syntax.ident ⟨1, sp, `x.y, none⟩,
  syntax.node ⟨2, sp, "ref", [
    syntax.ident ⟨3, sp, `x.y.z, none⟩
  ]⟩
]⟩

end lean

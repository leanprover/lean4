/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.data

namespace lean.parser

@[reducible] def syntax_id := ℕ
@[reducible] def macro_scope_id := ℕ

-- byte offset into source string
@[reducible] def position := ℕ

structure span :=
(left : position)
(right : position)
(file : string)

structure syntax_ident :=
(id : syntax_id) (sp : option span) (name : name) (msc : option macro_scope_id)

structure syntax_atom :=
(id : syntax_id) (sp : option span) (val : name)

structure syntax_node (syntax : Type) :=
(id : syntax_id) (sp : option span) (m : name) (args : list syntax)

inductive syntax
| ident (val : syntax_ident)
/- any non-ident atom -/
| atom (val : syntax_atom)
| list (ls : list syntax)
| node (val : syntax_node syntax)

protected meta def syntax.to_format : syntax → format :=
λ s, format.group $ format.nest 2 $ match s with
| (syntax.ident ident@{msc := none, ..}) := format!"({ident.id}: ident `{ident.name})"
| (syntax.ident ident@{msc := some sc, ..}) := format!"({ident.id}: ident `{ident.name} from {sc})"
| (syntax.atom atom) := format!"({atom.id}: atom {atom.val})"
| (syntax.list ls) := format!"[{format.join $ ls.map syntax.to_format}]"
| (syntax.node node) :=
    let args := format.join $ node.args.map (λ arg, format!"\n{arg.to_format}") in
    format!"({node.id}: node `{node.m} {args})"
end

meta instance : has_to_format syntax := ⟨syntax.to_format⟩
meta instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩
meta instance : has_repr syntax := ⟨to_string ∘ to_fmt⟩

end lean.parser

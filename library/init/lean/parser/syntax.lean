/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.lean.name

namespace lean
namespace parser

@[reducible] def syntax_id := ℕ
@[reducible] def macro_scope_id := ℕ

-- byte offset into source string
@[reducible] def offset := ℕ

structure span :=
(left  : offset)
(right : offset)
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
| lst  (ls : list syntax)
| node (val : syntax_node syntax)

namespace syntax
open format

protected mutual def to_format, to_format_lst
with to_format : syntax → format
| (ident {id := id, name := n, msc := none, ..}) :=
  paren (to_fmt id ++ ": ident " ++ to_fmt n)
| (ident {id := id, name := n, msc := some sc, ..}) :=
  paren (to_fmt id ++ ": ident " ++ to_fmt n  ++ " from " ++ to_fmt sc)
| (atom a) := paren (to_fmt a.id ++ ": atom " ++ to_fmt a.val)
| (lst ls) := paren $ join $ to_format_lst ls
| (node {id := id, m := n, args := args, ..}) :=
  paren (to_fmt id ++ ": node " ++ to_fmt n ++ join (to_format_lst args))
with to_format_lst : list syntax → list format
| []      := []
| (s::ss) := (line ++ to_format s) :: to_format_lst ss
end syntax

instance : has_to_format syntax := ⟨syntax.to_format⟩
instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩

end parser
end lean

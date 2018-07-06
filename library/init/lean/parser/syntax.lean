/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/
prelude
import init.lean.name init.lean.parser.parser_t

namespace lean
namespace parser

/-- De Bruijn index relative to surrounding 'bind' macros -/
@[reducible] def var_offset := ℕ
@[reducible] def macro_scope_id := ℕ

--TODO(Sebastian): move
structure substring :=
(start : string.iterator)
(stop : string.iterator)

structure source_info :=
(leading  : substring)
(pos      : position)
(trailing : substring)

structure resolved :=
-- local or (overloaded) global
(decl : var_offset ⊕ list name)
/- prefix of the reference that corresponds to the decl. All trailing name components
   are field accesses. -/
(«prefix» : name)

instance resolved.has_to_format : has_to_format resolved := ⟨λ r, to_fmt (r.decl, r.prefix)⟩

structure syntax_ident :=
(info : option source_info) (name : name) (msc : option macro_scope_id) (res : option resolved)

inductive atomic_val
| string (s : string)
| name   (n : name)

structure syntax_atom :=
(info : option source_info) (val : atomic_val)

structure syntax_node (syntax : Type) :=
(macro : name) (args : list syntax)

inductive syntax
| ident (val : syntax_ident)
/- any non-ident atom -/
| atom (val : syntax_atom)
| node (val : syntax_node syntax)

def substring.to_string (s : substring) : string :=
(s.start.extract s.stop).get_or_else ""

namespace syntax
open format

protected mutual def to_format, to_format_lst
with to_format : syntax → format
| (ident id) :=
  let n :=
    to_fmt id.name ++
    (match id.msc with
     | some msc := "!" ++ to_fmt msc
     | none := "") ++
    (match id.res with
     | some res :=
       ":" ++
       (match res.decl with
        | sum.inl idx := to_fmt idx
        | sum.inr [n] := to_fmt n
        | sum.inr ns  := to_fmt ns)
       ++ if res.prefix = id.name then
         to_fmt ""
       else
         to_fmt ".(" ++ to_fmt (id.name.replace_prefix res.prefix name.anonymous) ++ ")"
     | none := "") in
  n
| (atom ⟨_, atomic_val.string s⟩) := to_fmt $ repr s
| (atom ⟨_, atomic_val.name   n⟩) := to_fmt "`" ++ to_fmt n
| (node {macro := name.anonymous, args := args, ..}) :=
  sbracket $ join_sep (to_format_lst args) line
| (node {macro := n, args := args, ..}) :=
  paren $ join_sep (to_fmt n :: to_format_lst args) line
with to_format_lst : list syntax → list format
| []      := []
| (s::ss) := to_format s :: to_format_lst ss
end syntax

instance : has_to_format syntax := ⟨syntax.to_format⟩
instance : has_to_string syntax := ⟨to_string ∘ to_fmt⟩

end parser
end lean

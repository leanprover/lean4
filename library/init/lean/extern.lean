/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.expr init.data.option.basic

namespace lean

inductive extern_entry
| adhoc    (backend : name)
| inline   (backend : name) (pattern : string)
| standard (backend : name) (fn : string)
| foreign  (backend : name) (fn : string)

@[export lean.mk_adhoc_ext_entry_core]   def mk_adhoc_ext_entry   := extern_entry.adhoc
@[export lean.mk_inline_ext_entry_core]  def mk_inline_ext_entry  := extern_entry.inline
@[export lean.mk_std_ext_entry_core]     def mk_std_ext_entry     := extern_entry.standard
@[export lean.mk_foreign_ext_entry_core] def mk_foreign_ext_entry := extern_entry.foreign

/-
- `@[extern]`
   encoding: ```.entries = [adhoc `all]```
- `@[extern "level_hash"]`
   encoding: ```.entries = [standard `all "level_hash"]```
- `@[extern cpp "lean::string_size" llvm "lean_str_size"]`
   encoding: ```.entries = [standard `cpp "lean::string_size", standard `llvm "lean_str_size"]```
- `@[extern cpp inline "#1 + #2"]`
   encoding: ```.entries = [inline `cpp "#1 + #2"]```
- `@[extern cpp "foo" llvm adhoc]`
   encoding: ```.entries = [standard `cpp "foo", adhoc `llvm]```
- `@[extern 2 cpp "io_prim_println"]`
   encoding: ```.arity = 2, .entries = [standard `cpp "io_prim_println"]```
-/
structure extern_attr_data :=
(arity    : option nat := none)
(entries  : list extern_entry)

@[export lean.mk_extern_attr_data_core] def mk_extern_attr_data := extern_attr_data.mk

/-
Remark: we only support pattern parameters: #1 to #9. This should be more than enough,
and it simplifies the expander.
-/
def expand_extern_pattern_aux (args : list string) : nat → string.iterator → string → string
| 0     it r := r
| (i+1) it r :=
  if ¬ it.has_next then r
  else let c := it.curr in
    if c ≠ '#' then expand_extern_pattern_aux i it.next (r.push c)
    else
      let it  := it.next in
      let c   := it.curr in
      let j   := c.to_nat - '0'.to_nat - 1 in
      expand_extern_pattern_aux i it.next (r ++ (args.nth j).get_or_else "")

@[export lean.expand_extern_pattern_core]
def expand_extern_pattern (pattern : string) (args : list string) : string :=
expand_extern_pattern_aux args pattern.length pattern.mk_iterator ""

def mk_simple_fn_call (fn : string) (args : list string) : string :=
fn ++ "(" ++ ((args.intersperse ", ").foldl (++) "") ++ ")"

def expand_extern_entry : extern_entry → list string → option string
| (extern_entry.adhoc _) args        := none -- backend must expand it
| (extern_entry.standard _ fn) args  := some (mk_simple_fn_call fn args)
| (extern_entry.inline _ pat) args   := some (expand_extern_pattern pat args)
| (extern_entry.foreign _ fn) args   := some (mk_simple_fn_call fn args)

def extern_entry.backend : extern_entry → name
| (extern_entry.adhoc n)      := n
| (extern_entry.inline n _)   := n
| (extern_entry.standard n _) := n
| (extern_entry.foreign n _)  := n

def get_extern_entry_for_aux (backend : name) : list extern_entry → option extern_entry
| []      := none
| (e::es) :=
  if e.backend = `all then some e
  else if e.backend = backend then some e
  else get_extern_entry_for_aux es

@[export lean.get_extern_entry_for_core]
def get_extern_entry_for (d : extern_attr_data) (backend : name) : option extern_entry :=
get_extern_entry_for_aux backend d.entries

@[export lean.mk_extern_call_core]
def mk_extern_call (d : extern_attr_data) (backend : name) (args : list string) : option string :=
do e ← get_extern_entry_for d backend,
   expand_extern_entry e args

end lean

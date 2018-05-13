/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.parser init.lean.ir.type_check init.lean.ir.ssa_check
import init.lean.ir.extract_cpp init.lean.ir.format

/-
Frontend for compiling a file containing IR declarations into C++.
We use it for testing.
-/

namespace lean
namespace ir
open lean.parser

def parse_input_aux : nat → list decl → fnid_set → parser (list decl × fnid_set)
| 0     ds s := return (ds.reverse, s)
| (n+1) ds s :=
  (eoi >> return (ds.reverse, s))
  <|>
  (do m ← (symbol "nomangling" >> return tt) <|> return ff,
      d ← parse_decl,
      parse_input_aux n (d::ds) (if m then s.insert d.name else s))

def parse_input (s : string) : except format (list decl × fnid_set) :=
match parse (whitespace >> parse_input_aux s.length [] mk_fnid_set) s with
| except.ok r    := return r
| except.error m := throw (m.to_string s)

def check (env : environment) (d : decl) : except format unit :=
d.valid_ssa >> check_blockids d >> type_check d env >> return ()

local attribute [instance] name.has_lt_quick

def mk_env (ds : list decl) : environment :=
let m := ds.foldl (λ m d, rbmap.insert m d.name d) (mk_rbmap name decl (<)) in
λ n, m.find n

def mk_name_map (s : fnid_set) : fnid → option string :=
λ fid, if s.contains fid then some (to_string fid) else none

def lirc (s : string) : except format string :=
do (ds, s) ← parse_input s,
   let env := mk_env ds,
   let nm  := mk_name_map s,
   ds.mfor (check env),
   extract_cpp env nm ds

end ir
end lean

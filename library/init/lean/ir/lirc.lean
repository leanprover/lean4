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

def parse_input_aux : nat → list decl → fnid2string → parser (list decl × fnid2string)
| 0     ds m := return (ds.reverse, m)
| (n+1) ds m :=
  (eoi >> return (ds.reverse, m))
  <|>
  (do cid ← (do symbol "[", n ← lexeme $ c_identifier, symbol "]", return (some n)) <|> return none,
      d ← parse_decl,
      match cid with
      | some cid := parse_input_aux n (d::ds) (m.insert d.name cid)
      | none     := parse_input_aux n (d::ds) m)

def parse_input (s : string) : except format (list decl × fnid2string) :=
match parse (whitespace >> parse_input_aux s.length [] mk_fnid2string) s with
| except.ok r    := return r
| except.error m := throw (m.to_string s)

def check (env : environment) (d : decl) : except format unit :=
d.valid_ssa >> check_blockids d >> type_check d env >> return ()

local attribute [instance] name.has_lt_quick

def mk_env (ds : list decl) : environment :=
let m := ds.foldl (λ m d, rbmap.insert m d.name d) (mk_rbmap name decl (<)) in
λ n, m.find n

def lirc (s : string) (unit_name := "main") (unit_deps : list string := []) : except format string :=
do (ds, m) ← parse_input s,
   let env := mk_env ds,
   ds.mfor (check env),
   extract_cpp ds { env := env, external_names := m.find, unit_name := unit_name, unit_deps := unit_deps }

end ir
end lean

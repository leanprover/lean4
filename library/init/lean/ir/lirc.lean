/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.ir.parser init.lean.ir.type_check init.lean.ir.ssa_check
import init.lean.ir.extract_cpp init.lean.ir.format init.lean.ir.elim_phi

/-
Frontend for compiling a file containing IR declarations into C++.
We use it for testing.
-/

namespace lean
namespace ir
open lean.parser
open lean.parser.monad_parser

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
match parser_t.parse (whitespace >> parse_input_aux s.length [] mk_fnid2string) s with
| except.ok r    := return r
| except.error m := throw (m.to_string s)

def check (env : environment) (ssa : bool) (d : decl) : except format unit :=
when ssa (d.valid_ssa >> return ()) >> check_blockids d >> type_check d env >> return ()

local attribute [instance] name.has_lt_quick

def update_env (ds : list decl) (env : environment) : environment :=
let m := ds.foldl (λ m d, rbmap.insert m d.name d) (mk_rbmap name decl (<)) in
λ n, m.find n <|> env n

def update_external_names (m : fnid2string) (external_names : fnid → option string) : fnid → option string :=
λ n, m.find n <|> external_names n

def lirc (s : string) (cfg : extract_cpp_config := {}) (ssa := ff) : except format string :=
do (ds, m) ← parse_input s,
   let env := update_env ds cfg.env,
   let ext := update_external_names m cfg.external_names,
   ds.mfor (check env ssa),
   let ds := if ssa then ds.map elim_phi else ds,
   extract_cpp ds { env := env, external_names := ext, ..cfg }

end ir
end lean

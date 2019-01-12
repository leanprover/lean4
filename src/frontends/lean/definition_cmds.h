/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/decl_util.h"
namespace lean {
expr mk_equations(parser & p, buffer<expr> const & fns,
                  buffer<name> const & fn_full_names, buffer<name> const & fn_prv_names, buffer<expr> const & eqs,
                  optional<expr> const & wf_tacs, pos_info const & pos);

environment elab_defs(parser & p, decl_cmd_kind kind, cmd_meta const & meta, buffer <name> lp_names, buffer <expr> const & fns,
                      buffer <name> const & prv_names, buffer <expr> const & params, expr val, pos_info const & header_pos);

environment definition_cmd_core(parser & p, decl_cmd_kind k, cmd_meta const & meta);

environment ensure_decl_namespaces(environment const & env, name const & full_n);
}

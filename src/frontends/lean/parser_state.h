/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include <memory>
#include "util/name_generator.h"
#include "library/abstract_parser.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/local_level_decls.h"
#include "frontends/lean/local_context_adapter.h"
#include "frontends/lean/parser_pos_provider.h"
#include "library/util.h"

namespace lean {
typedef environment local_environment;

enum class id_behavior {
    /* Default: just generate an error when an undefined identifier is found */
    ErrorIfUndef,
    /* AssumeLocalIfNotLocal: if an identifier is not at m_local_decls tracked by the parser, then
       assume it is a local. We use that when parsing tactics. The identifiers that are not in m_local_decls
       are resolved at tactic execution time. */
    AssumeLocalIfNotLocal,
    /* AllLocal: assume that *all* identifiers (without level annotation) are local constants.
       We use this mode when we are parsing something that might be a pattern and/or expression */
    AllLocal,
    /* AssumeLocalIfUndef: assume an undefined identifier is a local constant, we use it when parsing quoted terms.
       We use this mode when converting t which might be a pattern and/or expression into a pattern.
       We perform the conversion *after* we parsed the term using AllLocal.
       Remark: we use ErrorIfUndef if we decide to convert it into a regular expression.
       Remark: This mode is different from AssumeLocalIfNotLocal, because it runs the whole name resolution
       procedure (including aliases, globals, etc). We cannot do this when processing tactics because
       global constants may be shadowed by the local context at tactic execution time. */
    AssumeLocalIfUndef};

struct snapshot;

class break_at_pos_exception : public std::exception {
public:
    enum class token_context {
        none, expr, notation, option, import, interactive_tactic, attribute, namespc, field, single_completion };
    struct token_info {
        pos_info           m_pos;
        name               m_token;

        token_context      m_context;
        name               m_param;
        optional<unsigned> m_tac_param_idx;
    };

    token_info m_token_info;
    optional<pos_info>   m_goal_pos;

    break_at_pos_exception(pos_info const & token_pos, name token = "",
                           token_context ctxt = break_at_pos_exception::token_context::none):
        m_token_info(token_info {token_pos, token, ctxt, {}, {}}) {}

    void report_goal_pos(pos_info goal_pos);
};

struct parser_scope {
    optional<options>          m_options;
    name_set                   m_level_variables;
    name_set                   m_variables;
    name_set                   m_include_vars;
    unsigned                   m_next_inst_idx;
    bool                       m_has_params;
    local_level_decls          m_local_level_decls;
    local_expr_decls           m_local_decls;
    parser_scope(optional<options> const & o, name_set const & lvs, name_set const & vs, name_set const & ivs,
                 unsigned next_inst_idx, bool has_params,
                 local_level_decls const & lld, local_expr_decls const & led):
        m_options(o), m_level_variables(lvs), m_variables(vs), m_include_vars(ivs),
        m_next_inst_idx(next_inst_idx), m_has_params(has_params),
        m_local_level_decls(lld), m_local_decls(led) {}
};

typedef list<parser_scope> parser_scope_stack;

/* For storing checkpoints in a file/buffer. This object is not exposed in the Lean API.  */
struct snapshot {
    environment        m_env;
    name_generator     m_ngen;
    local_level_decls  m_lds;
    local_expr_decls   m_eds;
    name_set           m_lvars; // subset of m_lds that is tagged as level variable
    name_set           m_vars; // subset of m_eds that is tagged as variable
    name_set           m_include_vars; // subset of m_eds that must be included
    options            m_options;
    bool               m_imports_parsed;
    bool               m_noncomputable_theory;
    parser_scope_stack m_parser_scope_stack;
    unsigned           m_next_inst_idx;
    pos_info           m_pos;
    snapshot(environment const & env, name_generator const & ngen, local_level_decls const & lds,
             local_expr_decls const & eds, name_set const & lvars, name_set const & vars,
             name_set const & includes, options const & opts, bool imports_parsed, bool noncomputable_theory, parser_scope_stack const & pss,
             unsigned next_inst_idx, pos_info const & pos):
        m_env(env), m_ngen(ngen), m_lds(lds), m_eds(eds), m_lvars(lvars), m_vars(vars), m_include_vars(includes),
        m_options(opts), m_imports_parsed(imports_parsed), m_noncomputable_theory(noncomputable_theory),
        m_parser_scope_stack(pss), m_next_inst_idx(next_inst_idx), m_pos(pos)
        {}
};
}

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include <memory>
#include "frontends/lean/scanner.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/local_level_decls.h"
#include "frontends/lean/local_context_adapter.h"
#include "frontends/lean/parser_pos_provider.h"

namespace lean {
class parser_state {
    /* \brief Extra data needed to be saved when we execute parser::push_local_scope */
    struct scope {
        optional<options>          m_options;
        name_set                   m_level_variables;
        name_set                   m_variables;
        name_set                   m_include_vars;
        unsigned                   m_num_undef_ids;
        unsigned                   m_next_inst_idx;
        bool                       m_has_params;
        local_level_decls          m_local_level_decls;
        local_expr_decls           m_local_decls;
        scope(optional<options> const & o, name_set const & lvs, name_set const & vs, name_set const & ivs,
              unsigned num_undef_ids, unsigned next_inst_idx, bool has_params,
              local_level_decls const & lld, local_expr_decls const & led):
            m_options(o), m_level_variables(lvs), m_variables(vs), m_include_vars(ivs),
            m_num_undef_ids(num_undef_ids), m_next_inst_idx(next_inst_idx), m_has_params(has_params),
            m_local_level_decls(lld), m_local_decls(led) {}
    };

    typedef list<scope> scope_stack;

    /* Read-only information */
    struct header {
        std::string               m_file_name;
        std::vector<token>        m_token_vector;
        optional<pos_info>        m_break_at_pos;
        name_set                  m_old_buckets_from_snapshot;
    };

    /* Context related stuff, it is not updated too often.
       We use copy-on-write optimization. */
    struct context {
        environment               m_env;
        io_state                  m_ios;
        local_level_decls         m_local_level_decls;
        local_expr_decls          m_local_decls;
        name_set                  m_level_variables;
        name_set                  m_variables; // subset of m_local_decls that is marked as variables
        name_set                  m_include_vars; // subset of m_local_decls that is marked as include
        scope_stack               m_scope_stack;
        scope_stack               m_quote_stack;
        list<expr>                m_undef_ids;
        /* Tasks that need to be successful (no exception) for parsing to succeed. */
        list<generic_task_result> m_required_successes;
    };

    typedef std::shared_ptr<header> header_ptr;
    typedef std::shared_ptr<context> context_ptr;

    header_ptr                    m_header;
    context_ptr                   m_context;
    pos_info_table                m_pos_table;
    /* Counters */
    unsigned                      m_tv_curr_idx;   /* current token being processed */
    unsigned                      m_tv_cmd_idx;    /* position of command token for the current command */
    unsigned                      m_next_tag_idx;  /* next expression tag */
    unsigned                      m_next_inst_idx; /* for anonymous instances */
    /* Flags */
    unsigned                      m_used_exceptions:1;
    unsigned                      m_has_params:1; // true context context contains parameters
    unsigned                      m_in_quote:1;
    unsigned                      m_in_pattern:1;
    unsigned                      m_found_errors:1;
    unsigned                      m_used_sorry:1;
    unsigned                      m_ignore_noncomputable:1;
    unsigned                      m_show_errors:1;
    unsigned                      m_complete:1;
    unsigned                      m_id_behavior:2;
};
}

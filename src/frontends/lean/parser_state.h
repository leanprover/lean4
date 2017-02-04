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

class snapshot;

class parser_state {
public:
    friend class parser;

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
        context(environment const & env, io_state const & ios):m_env(env), m_ios(ios) {}
    };

    typedef std::shared_ptr<header> header_ptr;
    typedef std::shared_ptr<context> context_ptr;

private:
    header_ptr                    m_header;
    context_ptr                   m_context;
    pos_info_table                m_pos_table;
    optional<pos_info>            m_break_at_pos;
    /* Counters */
    unsigned                      m_tv_curr_idx;   /* current token being processed */
    unsigned                      m_tv_cmd_idx;    /* position of command token for the current command */
    unsigned                      m_next_tag_idx;  /* next expression tag */
    unsigned                      m_next_inst_idx; /* for anonymous instances */
    /* Flags */
    unsigned                      m_use_exceptions:1;
    unsigned                      m_has_params:1; // true context context contains parameters
    unsigned                      m_in_quote:1;
    unsigned                      m_in_pattern:1;
    unsigned                      m_found_errors:1;
    unsigned                      m_used_sorry:1;
    unsigned                      m_ignore_noncomputable:1;
    unsigned                      m_complete:1;
    unsigned                      m_id_behavior:2;

public:
    parser_state(environment const & env, io_state const & ios, header_ptr const & h,
                 bool use_exceptions = false, std::shared_ptr<snapshot const> const & s = {});

    std::string const & get_file_name() const { return m_header->m_file_name; }

    std::vector<token> const & get_token_vector() const {
        return m_header->m_token_vector;
    }

    token const * lookahead(int delta) const;

    token const & curr_token() const { return get_token_vector()[m_tv_curr_idx]; }
    token_kind curr() const { return curr_token().kind(); }
    void next() { if (curr() != token_kind::Eof) m_tv_curr_idx++; }

    mpq const & get_num_val() const { return curr_token().get_num_val(); }
    name const & get_name_val() const { return curr_token().get_name_val(); }
    std::string const & get_str_val() const { return curr_token().get_str_val(); }
    token_info const & get_token_info() const { return curr_token().get_token_info(); }
};

typedef parser_state::scope parser_scope;
typedef list<parser_scope> parser_scope_stack;

/* For storing checkpoints in a file/buffer. This object is not exposed in the Lean API.  */
struct snapshot {
    environment        m_env;
    name_set           m_sub_buckets;
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
    list<generic_task_result> m_required_successes;
    snapshot(environment const & env, name_set const & sub_buckets, local_level_decls const & lds,
             local_expr_decls const & eds, name_set const & lvars, name_set const & vars,
             name_set const & includes, options const & opts, bool imports_parsed, bool noncomputable_theory, parser_scope_stack const & pss,
             unsigned next_inst_idx, pos_info const & pos, list<generic_task_result> const & required_successes):
        m_env(env), m_sub_buckets(sub_buckets), m_lds(lds), m_eds(eds), m_lvars(lvars), m_vars(vars), m_include_vars(includes),
        m_options(opts), m_imports_parsed(imports_parsed), m_noncomputable_theory(noncomputable_theory), m_parser_scope_stack(pss), m_next_inst_idx(next_inst_idx), m_pos(pos),
        m_required_successes(required_successes) {}
};

typedef std::vector<std::shared_ptr<snapshot const>> snapshot_vector;

}

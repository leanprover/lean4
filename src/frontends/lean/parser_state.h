/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include <memory>
#include "library/abstract_parser.h"
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

class break_at_pos_exception : public std::exception {
public:
    enum class token_context { none, expr, notation, option, import, interactive_tactic, attribute, namespc, field };
    struct token_info {
        pos_info      m_pos;
        name          m_token;

        token_context m_context;
        name          m_tac_class;
        name          m_struct; /* for field completion */
    };

    token_info m_token_info;
    optional<pos_info>   m_goal_pos;

    break_at_pos_exception(pos_info const & token_pos, name token = "",
                           token_context ctxt = break_at_pos_exception::token_context::none, name tac_class = {}):
        m_token_info(token_info {token_pos, token, ctxt, tac_class, name()}) {}

    void report_goal_pos(pos_info goal_pos);
};

class parser_state : public abstract_parser {
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
    virtual ~parser_state() {}

    environment const & env() const { return m_context->m_env; }

    virtual char const * get_file_name() const override { return m_header->m_file_name.c_str(); }

    std::vector<token> const & get_token_vector() const { return m_header->m_token_vector; }

    token const & curr_token() const { return get_token_vector()[m_tv_curr_idx]; }
    token_kind curr() const { return curr_token().kind(); }
    void next() { if (curr() != token_kind::Eof) m_tv_curr_idx++; }

    token const * lookahead(int delta) const;

    mpq const & get_num_val() const { return curr_token().get_num_val(); }
    name const & get_name_val() const { return curr_token().get_name_val(); }
    std::string const & get_str_val() const { return curr_token().get_str_val(); }
    token_info const & get_token_info() const { return curr_token().get_token_info(); }

    pos_info pos() const { return curr_token().get_pos(); }
    expr save_pos(expr e, pos_info p);
    expr rec_save_pos(expr const & e, pos_info p);
    expr update_pos(expr e, pos_info p);
    pos_info pos_of(expr const & e, pos_info default_pos) const;
    pos_info pos_of(expr const & e) const { return pos_of(e, pos()); }
    tag get_tag(expr e);
    expr copy_with_new_pos(expr const & e, pos_info p);

    /** \brief Return true iff the current token is an identifier */
    bool curr_is_identifier() const { return curr() == token_kind::Identifier; }
    /** \brief Return true iff the current token is a numeral */
    virtual bool curr_is_numeral() const final override { return curr() == token_kind::Numeral; }
    bool curr_is_decimal() const { return curr() == token_kind::Decimal; }
    /** \brief Return true iff the current token is a string */
    bool curr_is_string() const { return curr() == token_kind::String; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_keyword() const { return curr() == token_kind::Keyword; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_command() const { return curr() == token_kind::CommandKeyword; }
    /** \brief Return true iff the current token is EOF */
    bool curr_is_eof() const { return curr() == token_kind::Eof; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_quoted_symbol() const { return curr() == token_kind::QuotedSymbol; }
    /** \brief Return true iff the current token is a keyword named \c tk or an identifier named \c tk */
    bool curr_is_token_or_id(name const & tk) const;
    /** \brief Return true iff the current token is a command, EOF, period or script block */
    bool curr_is_command_like() const;
    /** \brief Read the next token if the current one is not End-of-file. */
    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    bool curr_is_token(name const & tk) const;
    /** \brief Check current token, and move to next characther, throw exception if current token is not \c tk. */
    void check_token_next(name const & tk, char const * msg);
    void check_token_or_id_next(name const & tk, char const * msg);
    /** \brief Check if the current token is an identifier, if it is return it and move to next token,
        otherwise throw an exception. */
    name check_id_next(char const * msg, break_at_pos_exception::token_context ctxt =
                       break_at_pos_exception::token_context::none);
    /** \brief Similar to check_id_next, but also ensures the identifier is *not* an internal/reserved name. */
    name check_decl_id_next(char const * msg, break_at_pos_exception::token_context ctxt =
                            break_at_pos_exception::token_context::none);
    /** \brief Check if the current token is an atomic identifier, if it is, return it and move to next token,
        otherwise throw an exception. */
    name check_atomic_id_next(char const * msg);
    name check_atomic_decl_id_next(char const * msg);
    list<name> to_constants(name const & id, char const * msg, pos_info const & p) const;
    name to_constant(name const & id, char const * msg, pos_info const & p);
    /** \brief Check if the current token is a constant, if it is, return it and move to next token, otherwise throw an exception. */
    name check_constant_next(char const * msg);


    void check_break_at_pos(break_at_pos_exception::token_context ctxt = break_at_pos_exception::token_context::none);
    /** \brief Throw \c break_at_pos_exception with empty token and given context if \c m_break_at_pos is before current
        position. */
    void check_break_before(break_at_pos_exception::token_context ctxt = break_at_pos_exception::token_context::none);

    name mk_anonymous_inst_name();
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

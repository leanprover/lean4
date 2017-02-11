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
#include "frontends/lean/parser_config.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/local_level_decls.h"
#include "frontends/lean/local_context_adapter.h"
#include "frontends/lean/parser_pos_provider.h"
#include "util/cancellable.h"

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
    enum class token_context { none, expr, notation, option, import, interactive_tactic, attribute, namespc, field };
    struct token_info {
        pos_info           m_pos;
        name               m_token;

        token_context      m_context;
        name               m_tac_class;
        optional<unsigned> m_tac_param_idx;
        name               m_struct; /* for field completion */
    };

    token_info m_token_info;
    optional<pos_info>   m_goal_pos;

    break_at_pos_exception(pos_info const & token_pos, name token = "",
                           token_context ctxt = break_at_pos_exception::token_context::none):
        m_token_info(token_info {token_pos, token, ctxt, {}, {}, {}}) {}

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
        unsigned                   m_next_inst_idx;
        bool                       m_has_params;
        local_level_decls          m_local_level_decls;
        local_expr_decls           m_local_decls;
        scope(optional<options> const & o, name_set const & lvs, name_set const & vs, name_set const & ivs,
              unsigned next_inst_idx, bool has_params,
              local_level_decls const & lld, local_expr_decls const & led):
            m_options(o), m_level_variables(lvs), m_variables(vs), m_include_vars(ivs),
            m_next_inst_idx(next_inst_idx), m_has_params(has_params),
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
        /* Tasks that need to be successful (no exception) for parsing to succeed. */
        list<gtask>               m_required_successes;
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

    void throw_parser_exception(char const * msg, pos_info p);
    void throw_nested_exception(throwable const & ex, pos_info p);

    void sync_command();
    void protected_call(std::function<void()> && f, std::function<void()> && sync);

    tag get_tag(expr e);
    expr copy_with_new_pos(expr const & e, pos_info p);

    parse_table const & nud() const { return get_nud_table(env()); }
    parse_table const & led() const { return get_led_table(env()); }

    unsigned curr_level_lbp() const;
    level parse_max_imax(bool is_max);
    level parse_level_id();
    level parse_level_nud();
    level parse_level_led(level left);

    void parse_doc_block();
    void parse_mod_doc_block();
    void check_no_doc_string();
    void reset_doc_string();

    void process_imports();
    void parse_command();
    task<bool> parse_commands();
    void process_postponed(buffer<expr> const & args, bool is_left, buffer<notation::action_kind> const & kinds,
                           buffer<list<expr>> const & nargs, buffer<expr> const & ps, buffer<pair<unsigned, pos_info>> const & scoped_info,
                           list<notation::action> const & postponed, pos_info const & p, buffer<expr> & new_args);
    expr parse_notation(parse_table t, expr * left);
    expr parse_nud_notation();
    expr parse_led_notation(expr left);
    expr parse_inaccessible();
    expr parse_placeholder();
    expr parse_anonymous_var_pattern();
    expr parse_nud();
    bool curr_starts_expr();
    expr parse_numeral_expr(bool user_notation = true);
    expr parse_decimal_expr();
    expr parse_string_expr();
    expr parse_char_expr();
    expr parse_inst_implicit_decl();
    void parse_inst_implicit_decl(buffer<expr> & r);
    expr parse_binder_core(binder_info const & bi, unsigned rbp);
    bool parse_binder_collection(buffer<pair<pos_info, name>> const & names, binder_info const & bi, buffer<expr> & r);
    void parse_binder_block(buffer<expr> & r, binder_info const & bi, unsigned rbp, bool allow_default);
    struct parse_binders_config {
        /* (input) If m_allow_empty is true, then parse_binders will succeed even if not binder is parsed. */
        bool     m_allow_empty{false};
        /* (input) right binding power */
        unsigned m_rbp{0};
        /* (input) If m_simple_only, then binder modifiers '{', '[' and '⦃' are not allowed. */
        bool     m_simple_only{false};
        /* (input) If true, it will allow binders of the form (x : T := v), and they will be converted
           into (x : opt_param T v) */
        bool     m_allow_default{false};
        /* (input and output)
          If m_infer_kind != nullptr, then a sequence of binders can be prefixed with '{}' or '()'
          Moreover, *m_infer_kind will be updated with

          - implicit_infer_kind::None if prefix is '()'
          - implicit_infer_kind::RelaxedImplicit if prefix is '{}'
          - implicit_infer_kind::Implicit, otherwise. */
        implicit_infer_kind * m_infer_kind{nullptr};
        /* (output) It is set to true if the last binder is surrounded
           with some kind of bracket (e.g., '()', '{}', '[]'). */
        bool     m_last_block_delimited{false};
        /* (output) If m_nentries != nullptr, then local notation declarations are stored here */
        buffer<notation_entry> * m_nentries{nullptr};
    };
    void parse_binders_core(buffer<expr> & r, parse_binders_config & cfg);
    local_environment parse_binders(buffer<expr> & r, parse_binders_config & cfg);
    bool parse_local_notation_decl(buffer<notation_entry> * entries);

    pair<optional<name>, expr> parse_id_tk_expr(name const & tk, unsigned rbp);

#if 0
    friend environment section_cmd(parser_state & p);
    friend environment context_cmd(parser_state & p);
    friend environment namespace_cmd(parser_state & p);
    friend environment end_scoped_cmd(parser_state & p);
#endif

    scope mk_scope(optional<options> const & opts = optional<options>());
    void restore_scope(scope const & s);

    bool has_local_scopes() const { return !is_nil(m_context->m_scope_stack); }
    void push_local_scope(bool save_options = true);
    void pop_local_scope();

    void ensure_exclusive_context();

    token const * get_last_cmd_tk() const;

public:
    parser_state(environment const & env, io_state const & ios, header_ptr const & h,
                 bool use_exceptions = false, std::shared_ptr<snapshot const> const & s = {});
    virtual ~parser_state() {}

    environment const & env() const { return m_context->m_env; }

    std::vector<token> const & get_token_vector() const { return m_header->m_token_vector; }
    token const & get_token(unsigned i) const { return m_header->m_token_vector[i]; }

    token const & curr_token() const { return get_token_vector()[m_tv_curr_idx]; }
    token_kind curr() const { return curr_token().kind(); }
    void next() override { if (curr() != token_kind::Eof) m_tv_curr_idx++; }

    token const * lookahead(int delta) const;

    mpq const & get_num_val() const { return curr_token().get_num_val(); }
    name const & get_name_val() const { return curr_token().get_name_val(); }
    std::string const & get_str_val() const { return curr_token().get_str_val(); }
    token_info const & get_token_info() const { return curr_token().get_token_info(); }

    pos_info pos() const override { return curr_token().get_pos(); }
    expr save_pos(expr e, pos_info p);
    expr rec_save_pos(expr const & e, pos_info p);
    expr update_pos(expr e, pos_info p);
    pos_info pos_of(expr const & e, pos_info default_pos) const;
    pos_info pos_of(expr const & e) const { return pos_of(e, pos()); }

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
    bool curr_is_token(name const & tk) const override;
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

    expr mk_app(expr fn, expr arg, pos_info const & p);
    expr mk_app(expr fn, buffer<expr> const & args, pos_info const & p);
    expr mk_app(std::initializer_list<expr> const & args, pos_info const & p);

    name mk_anonymous_inst_name();

    bool parse_local_notation_decl() { return parse_local_notation_decl(nullptr); }

    level parse_level(unsigned rbp = 0);

    expr parse_binder(unsigned rbp);

    local_environment parse_binders(buffer<expr> & r, bool & last_block_delimited) {
        parse_binders_config cfg;
        auto new_env = parse_binders(r, cfg);
        last_block_delimited = cfg.m_last_block_delimited;
        return new_env;
    }

    local_environment parse_binders(buffer<expr> & r, unsigned rbp, bool allow_default = false) {
        parse_binders_config cfg;
        cfg.m_rbp           = rbp;
        cfg.m_allow_default = allow_default;
        return parse_binders(r, cfg);
    }

    void parse_simple_binders(buffer<expr> & r, unsigned rbp) {
        parse_binders_config cfg;
        cfg.m_simple_only = true;
        cfg.m_rbp         = rbp;
        parse_binders(r, cfg);
    }

    local_environment parse_optional_binders(buffer<expr> & r, bool allow_default = false) {
        parse_binders_config cfg;
        cfg.m_allow_empty   = true;
        cfg.m_allow_default = allow_default;
        return parse_binders(r, cfg);
    }

    local_environment parse_optional_binders(buffer<expr> & r, implicit_infer_kind & kind) {
        parse_binders_config cfg;
        cfg.m_allow_empty   = true;
        cfg.m_infer_kind    = &kind;
        return parse_binders(r, cfg);
    }

    local_environment parse_binders(buffer<expr> & r, buffer<notation_entry> & nentries) {
        parse_binders_config cfg;
        cfg.m_nentries = &nentries;
        return parse_binders(r, cfg);
    }

    optional<binder_info> parse_optional_binder_info(bool simple_only = false);

    binder_info parse_binder_info(bool simple_only = false);
    void parse_close_binder_info(optional<binder_info> const & bi);
    void parse_close_binder_info(binder_info const & bi) { return parse_close_binder_info(optional<binder_info>(bi)); }

    /** \brief Convert an identifier into an expression (constant or local constant) based on the current scope */
    expr id_to_expr(name const & id, pos_info const & p, bool resolve_only = false);

    expr parse_expr(unsigned rbp = 0);
    /** \brief Parse an (optionally) qualified expression.
        If the input is of the form <id> : <expr>, then return the pair (some(id), expr).
        Otherwise, parse the next expression and return (none, expr). */
    pair<optional<name>, expr> parse_qualified_expr(unsigned rbp = 0);
    /** \brief If the input is of the form <id> := <expr>, then return the pair (some(id), expr).
        Otherwise, parse the next expression and return (none, expr). */
    pair<optional<name>, expr> parse_optional_assignment(unsigned rbp = 0);

    /** \brief Parse a pattern or expression */
    expr parse_pattern_or_expr(unsigned rbp = 0);
    /** \brief Convert an expression parsed using parse_pattern_or_expr into a pattern.
        The new local constants declared by the pattern are stored at new_locals.

        If skip_main_fn == true, then in the top-level application (f ...), the function f
        is not processed. */
    expr patexpr_to_pattern(expr const & pat_or_expr, bool skip_main_fn, buffer<expr> & new_locals);
    /** \brief Convert an expression parsed using parse_pattern_or_expr into a regular term. */
    expr patexpr_to_expr(expr const & pat_or_expr);
    expr parse_pattern(buffer<expr> & new_locals, unsigned rbp = 0) {
        return patexpr_to_pattern(parse_pattern_or_expr(rbp), false, new_locals);
    }
    /* \brief Set pattern mode, and invoke fn. The new locals are stored in new_locals */
    expr parse_pattern(std::function<expr(parser_state &)> const & fn, buffer<expr> & new_locals);

    expr parse_id();

    expr parse_led(expr left);
    expr parse_scoped_expr(unsigned num_params, expr const * ps, local_environment const & lenv, unsigned rbp = 0);
    expr parse_scoped_expr(buffer<expr> const & ps, local_environment const & lenv, unsigned rbp = 0) {
        return parse_scoped_expr(ps.size(), ps.data(), lenv, rbp);
    }
    expr parse_scoped_expr(unsigned num_params, expr const * ps, unsigned rbp = 0) {
        return parse_scoped_expr(num_params, ps, local_environment(m_context->m_env), rbp);
    }
    expr parse_scoped_expr(buffer<expr> const & ps, unsigned rbp = 0) { return parse_scoped_expr(ps.size(), ps.data(), rbp); }
    expr parse_expr_with_env(local_environment const & lenv, unsigned rbp = 0);

    expr parse_tactic(unsigned rbp = 0);

    struct local_scope {
        parser_state & m_p;
        environment    m_env;
        local_scope(parser_state & p, bool save_options = false);
        local_scope(parser_state & p, environment const & env);
        local_scope(parser_state & p, optional<environment> const & env);
        ~local_scope();
    };

    struct quote_scope {
        parser_state & m_p;
        id_behavior    m_id_behavior;
        bool           m_in_quote;
        bool           m_saved_in_pattern;
        quote_scope(parser_state & p, bool q);
        ~quote_scope();
    };

    bool in_quote() const { return m_in_quote; }

    void clear_expr_locals();
    bool has_locals() const { return !m_context->m_local_decls.empty() || !m_context->m_local_level_decls.empty(); }
    void add_local_level(name const & n, level const & l, bool is_variable = false);
    void add_local_expr(name const & n, expr const & p, bool is_variable = false);
    environment add_local_ref(environment const & env, name const & n, expr const & ref);
    void add_variable(name const & n, expr const & p);
    void add_parameter(name const & n, expr const & p);
    void add_local(expr const & p) { return add_local_expr(local_pp_name(p), p); }
    bool has_params() const { return m_has_params; }
    bool is_local_decl(expr const & l) const { return is_local(l) && m_context->m_local_decls.contains(local_pp_name(l)); }
    bool is_local_level_variable(name const & n) const { return m_context->m_level_variables.contains(n); }
    bool is_local_variable(name const & n) const { return m_context->m_variables.contains(n); }
    bool is_local_variable(expr const & e) const { return is_local_variable(local_pp_name(e)); }
    /** \brief Update binder information for the section parameter n, return true if success, and false if n is not a section parameter. */
    bool update_local_binder_info(name const & n, binder_info const & bi);
    void include_variable(name const & n) {
        ensure_exclusive_context();
        m_context->m_include_vars.insert(n);
    }
    void omit_variable(name const & n) {
        ensure_exclusive_context();
        m_context->m_include_vars.erase(n);
    }
    bool is_include_variable(name const & n) const { return m_context->m_include_vars.contains(n); }
    void get_include_variables(buffer<expr> & vars) const;
    /** \brief Position of the local level declaration named \c n in the sequence of local level decls. */
    unsigned get_local_level_index(name const & n) const { return m_context->m_local_level_decls.find_idx(n); }
    bool is_local_level(name const & n) const { return m_context->m_local_level_decls.contains(n); }
    /** \brief Position of the local declaration named \c n in the sequence of local decls. */
    unsigned get_local_index(name const & n) const;
    unsigned get_local_index(expr const & e) const { return get_local_index(local_pp_name(e)); }
    /** \brief Return the local parameter named \c n */
    expr const * get_local(name const & n) const { return m_context->m_local_decls.find(n); }
    /** \brief Return local declarations as a list of local constants. */
    list<expr> locals_to_context() const;
    /** \brief Return all local declarations and aliases */
    list<pair<name, expr>> const & get_local_entries() const { return m_context->m_local_decls.get_entries(); }
    /** \brief By default, when the parser finds a unknown identifier, it signs an error.
        These scope objects temporarily change this behavior. In any scope where this object
        is declared, the parse creates a constant/local even when the identifier is unknown.
        This behavior is useful when we are trying to parse mutually recursive declarations and
        tactics.
    */
    struct undef_id_to_local_scope : public flet<id_behavior> { undef_id_to_local_scope(parser_state &); };
    struct error_if_undef_scope : public flet<id_behavior> { error_if_undef_scope(parser_state & p); };
    struct all_id_local_scope : public flet<id_behavior> { all_id_local_scope(parser_state & p); };

private:
    pair<expr, level_param_names> elaborate(name const & decl_name, metavar_context & mctx, local_context_adapter const & adapter,
                                            expr const & e, bool check_unassigned = true);

public:
    local_context_adapter mk_local_context_adapter() { return local_context_adapter(m_context->m_local_decls); }
    pair<expr, level_param_names> elaborate(name const & decl_name, metavar_context & mctx, expr const & e, bool check_unassigned = true);
    pair<expr, level_param_names> elaborate(name const & decl_name, metavar_context & mctx, list<expr> const & lctx, expr const & e, bool check_unassigned);
    pair<expr, level_param_names> elaborate(name const & decl_name, list<expr> const & ctx, expr const & e);
    pair<expr, level_param_names> elaborate_type(name const & decl_name, list<expr> const & lctx, expr const & e);
    /* Elaborate \c e as a type using the given metavariable context, and using m_local_decls as the local context */
    pair<expr, level_param_names> elaborate_type(name const & decl_name, metavar_context & mctx, expr const & e);

    expr mk_sorry(pos_info const & p);
    bool used_sorry() const { return m_used_sorry; }
    void declare_sorry_if_used();

    void require_success(gtask const & t) {
        ensure_exclusive_context();
        m_context->m_required_successes = cons(t, m_context->m_required_successes);
    }

    /** return true iff profiling is enabled */
    bool profiling() const;

public:
    /* pos_info_provider API */
    virtual optional<pos_info> get_pos_info(expr const & e) const override;
    virtual pos_info get_some_pos() const override;
    virtual char const * get_file_name() const override { return m_header->m_file_name.c_str(); }
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
    list<gtask>        m_required_successes;
    cancellation_token m_cancellation_token;
    snapshot(environment const & env, name_set const & sub_buckets, local_level_decls const & lds,
             local_expr_decls const & eds, name_set const & lvars, name_set const & vars,
             name_set const & includes, options const & opts, bool imports_parsed, bool noncomputable_theory, parser_scope_stack const & pss,
             unsigned next_inst_idx, pos_info const & pos, list<gtask> const & required_successes, cancellation_token const & ctok):
        m_env(env), m_sub_buckets(sub_buckets), m_lds(lds), m_eds(eds), m_lvars(lvars), m_vars(vars), m_include_vars(includes),
        m_options(opts), m_imports_parsed(imports_parsed), m_noncomputable_theory(noncomputable_theory), m_parser_scope_stack(pss), m_next_inst_idx(next_inst_idx), m_pos(pos),
        m_required_successes(required_successes), m_cancellation_token(ctok) {}
};

typedef std::vector<std::shared_ptr<snapshot const>> snapshot_vector;
}

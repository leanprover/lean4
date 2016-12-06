/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/name_map.h"
#include "util/exception.h"
#include "kernel/environment.h"
#include "kernel/expr_maps.h"
#include "library/module.h"
#include "library/task_queue.h"
#include "library/abstract_parser.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/message_builder.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/local_level_decls.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/local_context_adapter.h"

namespace lean {
struct interrupt_parser {};
typedef environment             local_environment;
class metavar_context;
class local_context_adapter;
class scope_message_context;

/** \brief Extra data needed to be saved when we execute parser::push_local_scope */
struct parser_scope {
    optional<options>  m_options;
    name_set           m_level_variables;
    name_set           m_variables;
    name_set           m_include_vars;
    unsigned           m_num_undef_ids;
    unsigned           m_next_inst_idx;
    bool               m_has_params;
    local_level_decls  m_local_level_decls;
    local_expr_decls   m_local_decls;
    parser_scope(optional<options> const & o, name_set const & lvs, name_set const & vs, name_set const & ivs,
                 unsigned num_undef_ids, unsigned next_inst_idx, bool has_params,
                 local_level_decls const & lld, local_expr_decls const & led):
        m_options(o), m_level_variables(lvs), m_variables(vs), m_include_vars(ivs),
        m_num_undef_ids(num_undef_ids), m_next_inst_idx(next_inst_idx), m_has_params(has_params),
        m_local_level_decls(lld), m_local_decls(led) {}
};
typedef list<parser_scope> parser_scope_stack;

/** \brief Snapshot of the state of the Lean parser */
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
    parser_scope_stack m_parser_scope_stack;
    pos_info           m_pos;
    snapshot(environment const & env, name_set const & sub_buckets, local_level_decls const & lds,
             local_expr_decls const & eds, name_set const & lvars, name_set const & vars,
             name_set const & includes, options const & opts, bool imports_parsed, parser_scope_stack const & pss,
             pos_info const & pos):
        m_env(env), m_sub_buckets(sub_buckets), m_lds(lds), m_eds(eds), m_lvars(lvars), m_vars(vars), m_include_vars(includes),
        m_options(opts), m_imports_parsed(imports_parsed), m_parser_scope_stack(pss), m_pos(pos) {}
};

typedef std::vector<std::shared_ptr<snapshot const>> snapshot_vector;

class show_goal_exception : public std::exception {
public:
    pos_info m_pos;
    tactic_state m_state;

    show_goal_exception(pos_info const & pos, tactic_state const & goal) : m_pos(pos), m_state(goal) {}
};

enum class id_behavior {
    ErrorIfUndef, /* Default: just generate an error when an undefined identifier is found */
    AssumeConstantIfUndef, /* Assume an undefined identifier is a constant, we use it for parsing inductive datatypes. */
    AssumeLocalIfUndef, /* Assume an undefined identifier is a local constant, we use it when parsing quoted terms. */
    AllLocal    /* Assume that *all* identifiers (without level annotation) are local constants. */ };

class parser : public abstract_parser {
    environment             m_env;
    io_state                m_ios;
    bool                    m_verbose;
    bool                    m_use_exceptions;
    bool                    m_show_errors;
    module_loader           m_import_fn;
    std::string             m_file_name;
    scanner                 m_scanner;
    scanner::token_kind     m_curr;
    local_level_decls       m_local_level_decls;
    local_expr_decls        m_local_decls;
    bool                    m_has_params; // true context context contains parameters
    name_set                m_level_variables;
    name_set                m_variables; // subset of m_local_decls that is marked as variables
    name_set                m_include_vars; // subset of m_local_decls that is marked as include
    bool                    m_imports_parsed;
    parser_scope_stack      m_parser_scope_stack;
    parser_scope_stack      m_quote_stack;
    bool                    m_in_quote;
    bool                    m_in_pattern;
    pos_info                m_last_cmd_pos;
    unsigned                m_next_tag_idx;
    unsigned                m_next_inst_idx;
    bool                    m_found_errors;
    bool                    m_used_sorry;
    pos_info_table          m_pos_table;
    // By default, when the parser finds a unknown identifier, it signs an error.
    // When the following flag is true, it creates a constant.
    // This flag is when we are trying to parse mutually recursive declarations.
    id_behavior             m_id_behavior;

    // info support
    snapshot_vector *       m_snapshot_vector;
    name_set                m_old_buckets_from_snapshot;

    // curr command token
    name                   m_cmd_token;

    buffer<expr>           m_undef_ids;

    // profiling
    bool                   m_profile;

    // stop/info at line/col
    bool                   m_stop_at; // if true, then parser stops execution after the given line and column is reached
    unsigned               m_stop_at_line;
    bool                   m_info_at;
    unsigned               m_info_at_line;
    unsigned               m_info_at_col;

    // If the following flag is true we do not raise error messages
    // noncomputable definitions not tagged as noncomputable.
    bool                   m_ignore_noncomputable;

    // Docgen
    optional<std::string>  m_doc_string;

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

    std::vector<module_name> parse_imports(unsigned & fingerprint);
    void process_imports();
    void parse_command();
    bool parse_commands();
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
    void parse_binder_block(buffer<expr> & r, binder_info const & bi, unsigned rbp);
    void parse_binders_core(buffer<expr> & r, buffer<notation_entry> * nentries, bool & last_block_delimited, unsigned rbp, bool simple_only);
    local_environment parse_binders(buffer<expr> & r, buffer<notation_entry> * nentries, bool & last_block_delimited,
                                    bool allow_empty, unsigned rbp, bool simple_only);
    bool parse_local_notation_decl(buffer<notation_entry> * entries);

    pair<optional<name>, expr> parse_id_tk_expr(name const & tk, unsigned rbp);

    friend environment section_cmd(parser & p);
    friend environment context_cmd(parser & p);
    friend environment namespace_cmd(parser & p);
    friend environment end_scoped_cmd(parser & p);

    parser_scope mk_parser_scope(optional<options> const & opts = optional<options>());
    void restore_parser_scope(parser_scope const & s);

    void push_local_scope(bool save_options = true);
    void pop_local_scope();

    void save_snapshot(scope_message_context &);

public:
    parser(environment const & env, io_state const & ios,
           module_loader const & import_fn,
           std::istream & strm, std::string const & file_name,
           bool use_exceptions = false,
           std::shared_ptr<snapshot const> const & s = {}, snapshot_vector * sv = nullptr);
    ~parser();

    void enable_show_goal(pos_info const & pos);
    void enable_show_info(pos_info const & pos);

    bool ignore_noncomputable() const { return m_ignore_noncomputable; }
    void set_ignore_noncomputable() { m_ignore_noncomputable = true; }

    bool found_errors() const { return m_found_errors; }

    name mk_anonymous_inst_name();
    bool is_anonymous_inst_name(name const & n) const;

    unsigned curr_lbp() const;

    cmd_table const & cmds() const { return get_cmd_table(env()); }

    environment const & env() const { return m_env; }
    io_state const & ios() const { return m_ios; }

    message_builder mk_message(pos_info const & p, message_severity severity);
    message_builder mk_message(message_severity severity);

    local_level_decls const & get_local_level_decls() const { return m_local_level_decls; }
    local_expr_decls const & get_local_expr_decls() const { return m_local_decls; }

    void updt_options();
    options get_options() const { return m_ios.get_options(); }
    template<typename T> void set_option(name const & n, T const & v) { m_ios.set_option(n, v); }

    /** \brief Return the current position information */
    virtual pos_info pos() const override final { return pos_info(m_scanner.get_line(), m_scanner.get_pos()); }
    expr save_pos(expr e, pos_info p);
    expr rec_save_pos(expr const & e, pos_info p);
    expr update_pos(expr e, pos_info p);
    pos_info pos_of(expr const & e, pos_info default_pos) const;
    pos_info pos_of(expr const & e) const { return pos_of(e, pos()); }
    pos_info cmd_pos() const { return m_last_cmd_pos; }
    name const & get_cmd_token() const { return m_cmd_token; }

    optional<std::string> get_doc_string() const { return m_doc_string; }

    parser_pos_provider get_parser_pos_provider(pos_info const & some_pos) const {
        return parser_pos_provider(m_pos_table, m_file_name, some_pos);
    }

    expr mk_app(expr fn, expr arg, pos_info const & p);
    expr mk_app(expr fn, buffer<expr> const & args, pos_info const & p);
    expr mk_app(std::initializer_list<expr> const & args, pos_info const & p);

    /** \brief Read the next token. */
    void scan();
    /** \brief Return the current token */
    scanner::token_kind curr() const { return m_curr; }
    /** \brief Return true iff the current token is an identifier */
    bool curr_is_identifier() const { return curr() == scanner::token_kind::Identifier; }
    /** \brief Return true iff the current token is a numeral */
    virtual bool curr_is_numeral() const final override { return curr() == scanner::token_kind::Numeral; }
    bool curr_is_decimal() const { return curr() == scanner::token_kind::Decimal; }
    /** \brief Return true iff the current token is a string */
    bool curr_is_string() const { return curr() == scanner::token_kind::String; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_keyword() const { return curr() == scanner::token_kind::Keyword; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_command() const { return curr() == scanner::token_kind::CommandKeyword; }
    /** \brief Return true iff the current token is EOF */
    bool curr_is_eof() const { return curr() == scanner::token_kind::Eof; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_quoted_symbol() const { return curr() == scanner::token_kind::QuotedSymbol; }
    /** \brief Return true iff the current token is a keyword named \c tk or an identifier named \c tk */
    bool curr_is_token_or_id(name const & tk) const;
    /** \brief Return true iff the current token is a command, EOF, period or script block */
    bool curr_is_command_like() const;
    /** \brief Read the next token if the current one is not End-of-file. */
    virtual void next() override final { if (m_curr != scanner::token_kind::Eof) scan(); }
    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    virtual bool curr_is_token(name const & tk) const override final;
    /** \brief Check current token, and move to next characther, throw exception if current token is not \c tk. */
    void check_token_next(name const & tk, char const * msg);
    void check_token_or_id_next(name const & tk, char const * msg);
    /** \brief Check if the current token is an identifier, if it is return it and move to next token,
        otherwise throw an exception. */
    name check_id_next(char const * msg);
    /** \brief Similar to check_id_next, but also ensures the identifier is *not* an internal/reserved name. */
    name check_decl_id_next(char const * msg);
    /** \brief Check if the current token is an atomic identifier, if it is, return it and move to next token,
        otherwise throw an exception. */
    name check_atomic_id_next(char const * msg);
    name check_atomic_decl_id_next(char const * msg);
    list<name> to_constants(name const & id, char const * msg, pos_info const & p) const;
    name to_constant(name const & id, char const * msg, pos_info const & p);
    /** \brief Check if the current token is a constant, if it is, return it and move to next token, otherwise throw an exception. */
    name check_constant_next(char const * msg);

    mpq const & get_num_val() const { return m_scanner.get_num_val(); }
    name const & get_name_val() const { return m_scanner.get_name_val(); }
    std::string const & get_str_val() const { return m_scanner.get_str_val(); }
    token_info const & get_token_info() const { return m_scanner.get_token_info(); }
    std::string const & get_stream_name() const { return m_scanner.get_stream_name(); }

    unsigned get_small_nat();
    virtual unsigned parse_small_nat() override final;
    virtual std::string parse_string_lit() override final;
    virtual name_map<std::string> parse_kv_pairs() override final;
    double parse_double();

    bool parse_local_notation_decl() { return parse_local_notation_decl(nullptr); }

    level parse_level(unsigned rbp = 0);

    expr parse_binder(unsigned rbp);
    local_environment parse_binders(buffer<expr> & r, bool & last_block_delimited) {
        unsigned rbp = 0; bool allow_empty = false; bool simple_only = false;
        return parse_binders(r, nullptr, last_block_delimited, allow_empty, rbp, simple_only);
    }
    local_environment parse_binders(buffer<expr> & r, unsigned rbp) {
        bool tmp; bool allow_empty = false; bool simple_only = false;
        return parse_binders(r, nullptr, tmp, allow_empty, rbp, simple_only);
    }
    void parse_simple_binders(buffer<expr> & r, unsigned rbp) {
        bool tmp; bool allow_empty = false; bool simple_only = true;
        parse_binders(r, nullptr, tmp, allow_empty, rbp, simple_only);
    }
    local_environment parse_optional_binders(buffer<expr> & r) {
        bool tmp; bool allow_empty = true; unsigned rbp = 0; bool simple_only = false;
        return parse_binders(r, nullptr, tmp, allow_empty, rbp, simple_only);
    }
    local_environment parse_binders(buffer<expr> & r, buffer<notation_entry> & nentries) {
        bool tmp; bool allow_empty = false; unsigned rbp = 0; bool simple_only = false;
        return parse_binders(r, &nentries, tmp, allow_empty, rbp, simple_only);
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
    expr parse_pattern(std::function<expr(parser &)> const & fn, buffer<expr> & new_locals);

    expr parse_id();

    expr parse_led(expr left);
    expr parse_scoped_expr(unsigned num_params, expr const * ps, local_environment const & lenv, unsigned rbp = 0);
    expr parse_scoped_expr(buffer<expr> const & ps, local_environment const & lenv, unsigned rbp = 0) {
        return parse_scoped_expr(ps.size(), ps.data(), lenv, rbp);
    }
    expr parse_scoped_expr(unsigned num_params, expr const * ps, unsigned rbp = 0) {
        return parse_scoped_expr(num_params, ps, local_environment(m_env), rbp);
    }
    expr parse_scoped_expr(buffer<expr> const & ps, unsigned rbp = 0) { return parse_scoped_expr(ps.size(), ps.data(), rbp); }
    expr parse_expr_with_env(local_environment const & lenv, unsigned rbp = 0);

    expr parse_tactic(unsigned rbp = 0);

    struct local_scope {
        parser & m_p; environment m_env;
        local_scope(parser & p, bool save_options = false);
        local_scope(parser & p, environment const & env);
        local_scope(parser & p, optional<environment> const & env);
        ~local_scope();
    };

    struct quote_scope {
        parser &    m_p;
        id_behavior m_id_behavior;
        bool        m_in_quote;
        bool        m_saved_in_pattern;
        quote_scope(parser & p, bool q);
        ~quote_scope();
    };

    bool in_quote() const { return m_in_quote; }

    void clear_locals();
    bool has_locals() const { return !m_local_decls.empty() || !m_local_level_decls.empty(); }
    void add_local_level(name const & n, level const & l, bool is_variable = false);
    void add_local_expr(name const & n, expr const & p, bool is_variable = false);
    environment add_local_ref(environment const & env, name const & n, expr const & ref);
    void add_variable(name const & n, expr const & p);
    void add_parameter(name const & n, expr const & p);
    void add_local(expr const & p) { return add_local_expr(local_pp_name(p), p); }
    bool has_params() const { return m_has_params; }
    bool is_local_decl(expr const & l) const { return is_local(l) && m_local_decls.contains(local_pp_name(l)); }
    bool is_local_level_variable(name const & n) const { return m_level_variables.contains(n); }
    bool is_local_variable(name const & n) const { return m_variables.contains(n); }
    bool is_local_variable(expr const & e) const { return is_local_variable(local_pp_name(e)); }
    /** \brief Update binder information for the section parameter n, return true if success, and false if n is not a section parameter. */
    bool update_local_binder_info(name const & n, binder_info const & bi);
    void include_variable(name const & n) { m_include_vars.insert(n); }
    void omit_variable(name const & n) { m_include_vars.erase(n); }
    bool is_include_variable(name const & n) const { return m_include_vars.contains(n); }
    void get_include_variables(buffer<expr> & vars) const;
    /** \brief Position of the local level declaration named \c n in the sequence of local level decls. */
    unsigned get_local_level_index(name const & n) const { return m_local_level_decls.find_idx(n); }
    bool is_local_level(name const & n) const { return m_local_level_decls.contains(n); }
    /** \brief Position of the local declaration named \c n in the sequence of local decls. */
    unsigned get_local_index(name const & n) const;
    unsigned get_local_index(expr const & e) const { return get_local_index(local_pp_name(e)); }
    /** \brief Return the local parameter named \c n */
    expr const * get_local(name const & n) const { return m_local_decls.find(n); }
    /** \brief Return local declarations as a list of local constants. */
    list<expr> locals_to_context() const;
    /** \brief Return all local declarations and aliases */
    list<pair<name, expr>> const & get_local_entries() const { return m_local_decls.get_entries(); }
    /** \brief By default, when the parser finds a unknown identifier, it signs an error.
        These scope objects temporarily change this behavior. In any scope where this object
        is declared, the parse creates a constant/local even when the identifier is unknown.
        This behavior is useful when we are trying to parse mutually recursive declarations and
        tactics.
    */
    struct undef_id_to_const_scope : public flet<id_behavior> { undef_id_to_const_scope(parser & p); };
    struct undef_id_to_local_scope : public flet<id_behavior> { undef_id_to_local_scope(parser &); };
    struct error_if_undef_scope : public flet<id_behavior> { error_if_undef_scope(parser & p); };
    struct all_id_local_scope : public flet<id_behavior> { all_id_local_scope(parser & p); };

    /** \brief Return the size of the stack of undefined local constants */
    unsigned get_num_undef_ids() const { return m_undef_ids.size(); }
    /** \brief Return the i-th undefined local constants */
    expr const & get_undef_id(unsigned i) const { return m_undef_ids[i]; }

private:
    pair<expr, level_param_names> elaborate(metavar_context & mctx, local_context_adapter const & adapter,
                                            expr const & e, bool check_unassigned = true);

public:
    local_context_adapter mk_local_context_adapter() { return local_context_adapter(m_local_decls); }
    pair<expr, level_param_names> elaborate(expr const & e);
    pair<expr, level_param_names> elaborate(metavar_context & mctx, expr const & e, bool check_unassigned = true);
    pair<expr, level_param_names> elaborate(metavar_context & mctx, list<expr> const & lctx, expr const & e, bool check_unassigned);
    pair<expr, level_param_names> elaborate(list<expr> const & ctx, expr const & e);
    pair<expr, level_param_names> elaborate_type(list<expr> const & lctx, expr const & e);
    /* Elaborate \c e as a type using the given metavariable context, and using m_local_decls as the local context */
    pair<expr, level_param_names> elaborate_type(metavar_context & mctx, expr const & e);

    expr mk_sorry(pos_info const & p);
    bool used_sorry() const { return m_used_sorry; }

    /** return true iff profiling is enabled */
    bool profiling() const { return m_profile; }

    /** parse all commands in the input stream */
    bool operator()() { return parse_commands(); }

    std::vector<module_name> get_imports();

    class in_notation_ctx {
        scanner::in_notation_ctx m_ctx;
    public:
        in_notation_ctx(parser & p):m_ctx(p.m_scanner) {}
    };

public:
    /* pos_info_provider API */
    virtual optional<pos_info> get_pos_info(expr const & e) const override;
    virtual pos_info get_some_pos() const override;
    virtual char const * get_file_name() const override;
};

bool parse_commands(environment & env, io_state & ios, char const * fname);

void initialize_parser();
void finalize_parser();
}

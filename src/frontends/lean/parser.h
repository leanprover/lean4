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
#include "util/script_state.h"
#include "util/name_map.h"
#include "util/exception.h"
#include "util/thread_script_state.h"
#include "util/script_exception.h"
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/expr_maps.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/kernel_bindings.h"
#include "library/definition_cache.h"
#include "library/declaration_index.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/elaborator_context.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/parser_pos_provider.h"
#include "frontends/lean/theorem_queue.h"
#include "frontends/lean/info_manager.h"

namespace lean {
/** \brief Exception used to track parsing erros, it does not leak outside of this class. */
struct parser_error : public exception {
    pos_info m_pos;
    parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
    parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
    virtual throwable * clone() const { return new parser_error(m_msg.c_str(), m_pos); }
    virtual void rethrow() const { throw *this; }
};

struct interrupt_parser {};
typedef local_decls<expr>       local_expr_decls;
typedef local_decls<level>      local_level_decls;
typedef environment             local_environment;

/** \brief Extra data needed to be saved when we execute parser::push_local_scope */
struct parser_scope_stack_elem {
    optional<options>  m_options;
    name_set           m_level_variables;
    name_set           m_variables;
    name_set           m_include_vars;
    unsigned           m_num_undef_ids;
    bool               m_has_params;
    local_level_decls  m_local_level_decls;
    local_expr_decls   m_local_decls;
    parser_scope_stack_elem(optional<options> const & o, name_set const & lvs, name_set const & vs, name_set const & ivs,
                            unsigned num_undef_ids, bool has_params,
                            local_level_decls const & lld, local_expr_decls const & led):
        m_options(o), m_level_variables(lvs), m_variables(vs), m_include_vars(ivs),
        m_num_undef_ids(num_undef_ids), m_has_params(has_params), m_local_level_decls(lld), m_local_decls(led) {}
};
typedef list<parser_scope_stack_elem> parser_scope_stack;

/** \brief Snapshot of the state of the Lean parser */
struct snapshot {
    environment        m_env;
    name_generator     m_ngen;
    local_level_decls  m_lds;
    local_expr_decls   m_eds;
    name_set           m_lvars; // subset of m_lds that is tagged as level variable
    name_set           m_vars; // subset of m_eds that is tagged as variable
    name_set           m_include_vars; // subset of m_eds that must be included
    options            m_options;
    parser_scope_stack m_parser_scope_stack;
    unsigned           m_line;
    snapshot():m_line(0) {}
    snapshot(environment const & env, options const & o):m_env(env), m_options(o), m_line(1) {}
    snapshot(environment const & env, name_generator const & ngen, local_level_decls const & lds,
             local_expr_decls const & eds, name_set const & lvars, name_set const & vars,
             name_set const & includes, options const & opts, parser_scope_stack const & pss, unsigned line):
        m_env(env), m_ngen(ngen), m_lds(lds), m_eds(eds), m_lvars(lvars), m_vars(vars), m_include_vars(includes),
        m_options(opts), m_parser_scope_stack(pss), m_line(line) {}
};

typedef std::vector<snapshot> snapshot_vector;

enum class keep_theorem_mode { All, DiscardImported, DiscardAll };

enum class undef_id_behavior { Error, AssumeConstant, AssumeLocal };

class parser {
    environment             m_env;
    io_state                m_ios;
    name_generator          m_ngen;
    bool                    m_verbose;
    bool                    m_use_exceptions;
    bool                    m_show_errors;
    unsigned                m_num_threads;
    scanner                 m_scanner;
    scanner::token_kind     m_curr;
    local_level_decls       m_local_level_decls;
    local_expr_decls        m_local_decls;
    bool                    m_has_params; // true context context contains parameters
    name_set                m_level_variables;
    name_set                m_variables; // subset of m_local_decls that is marked as variables
    name_set                m_include_vars; // subset of m_local_decls that is marked as include
    parser_scope_stack      m_parser_scope_stack;
    pos_info                m_last_cmd_pos;
    pos_info                m_last_script_pos;
    unsigned                m_next_tag_idx;
    bool                    m_found_errors;
    bool                    m_used_sorry;
    pos_info_table          m_pos_table;
    // By default, when the parser finds a unknown identifier, it signs an error.
    // When the following flag is true, it creates a constant.
    // This flag is when we are trying to parse mutually recursive declarations.
    undef_id_behavior       m_undef_id_behavior;
    optional<bool>          m_has_num;
    optional<bool>          m_has_string;
    optional<bool>          m_has_tactic_decls;
    // We process theorems in parallel
    theorem_queue           m_theorem_queue;
    name_set                m_theorem_queue_set; // set of theorem names in m_theorem_queue

    // info support
    snapshot_vector *       m_snapshot_vector;
    info_manager *          m_info_manager;
    info_manager            m_pre_info_manager; // type information before elaboration

    // cache support
    definition_cache *     m_cache;
    // index support
    declaration_index *    m_index;

    keep_theorem_mode      m_keep_theorem_mode;

    // curr command token
    name                   m_cmd_token;

    buffer<expr>           m_undef_ids;

    // profiling
    bool                   m_profile;

    // auxiliary field used to record the size of m_local_decls before a command is executed.
    unsigned               m_local_decls_size_at_beg_cmd;

    // stop/info at line/col
    bool                   m_stop_at; // if true, then parser stops execution after the given line and column is reached
    unsigned               m_stop_at_line;
    bool                   m_info_at;
    unsigned               m_info_at_line;
    unsigned               m_info_at_col;

    // If the following flag is true we do not raise error messages
    // noncomputable definitions not tagged as noncomputable.
    bool                   m_ignore_noncomputable;

    void display_warning_pos(unsigned line, unsigned pos);
    void display_error_pos(unsigned line, unsigned pos);
    void display_error_pos(pos_info p);
    void display_error(char const * msg, unsigned line, unsigned pos);
    void display_error(char const * msg, pos_info p);
    void display_error(throwable const & ex);
    void display_error(script_exception const & ex);
    void throw_parser_exception(char const * msg, pos_info p);
    void throw_nested_exception(throwable const & ex, pos_info p);

    void sync_command();
    void protected_call(std::function<void()> && f, std::function<void()> && sync);
    template<typename F>
    typename std::result_of<F(lua_State * L)>::type using_script(F && f) {
        try {
            script_state S = get_thread_script_state();
            set_io_state    set1(S, m_ios);
            set_environment set2(S, m_env);
            return f(S.get_state());
        } catch (script_nested_exception & ex) {
            ex.get_exception().rethrow();
        }
    }

    tag get_tag(expr e);
    expr copy_with_new_pos(expr const & e, pos_info p);

    parse_table const & nud() const { return get_nud_table(env()); }
    parse_table const & led() const { return get_led_table(env()); }
    parse_table const & tactic_nud() const { return get_tactic_nud_table(env()); }
    parse_table const & tactic_led() const { return get_tactic_led_table(env()); }

    unsigned curr_level_lbp() const;
    level parse_max_imax(bool is_max);
    level parse_level_id();
    level parse_level_nud();
    level parse_level_led(level left);

    void parse_imports();
    void parse_command();
    void parse_script(bool as_expr = false);
    bool parse_commands();
    unsigned curr_lbp_core(bool as_tactic) const;
    expr parse_notation_core(parse_table t, expr * left, bool as_tactic);
    expr parse_expr_or_tactic(unsigned rbp, bool as_tactic) {
        return as_tactic ? parse_tactic(rbp) : parse_expr(rbp);
    }
    expr parse_notation(parse_table t, expr * left) { return parse_notation_core(t, left, false); }
    expr parse_tactic_notation(parse_table t, expr * left) { return parse_notation_core(t, left, true); }
    expr parse_nud_notation();
    expr parse_led_notation(expr left);
    expr parse_nud();
    expr parse_numeral_expr(bool user_notation = true);
    expr parse_decimal_expr();
    expr parse_string_expr();
    expr parse_binder_core(binder_info const & bi, unsigned rbp);
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

    void push_local_scope(bool save_options = false);
    void pop_local_scope();

    void save_snapshot();
    void save_overload(expr const & e);
    void save_overload_notation(list<expr> const & as, pos_info const & p);
    void save_overload_notation(list<pair<unsigned, expr>> const & as, pos_info const & p);
    void save_type_info(expr const & e);
    void save_pre_info_data();
    void save_identifier_info(pos_info const & p, name const & full_id);
    void commit_info(unsigned line, unsigned col);
    void commit_info() { commit_info(m_scanner.get_line(), m_scanner.get_pos()); }

    elaborator_context mk_elaborator_context(pos_info_provider const & pp, bool check_unassigned = true);
    elaborator_context mk_elaborator_context(environment const & env, pos_info_provider const & pp);
    elaborator_context mk_elaborator_context(environment const & env, local_level_decls const & lls, pos_info_provider const & pp);

    bool m_in_backtick; // true if parser `expr` notation
    expr parse_backtick_expr_core();
    expr parse_backtick_expr();

    optional<expr> is_tactic_command(name & id);
    expr parse_tactic_option_num();
    expr parse_tactic_led(expr left);
    expr parse_tactic_nud();
    expr mk_tactic_expr_list(buffer<expr> const & args, pos_info const & p);
    expr parse_tactic_expr_list();
    expr parse_tactic_opt_expr_list();
    expr parse_tactic_id_list();
    expr parse_tactic_opt_id_list();
    expr parse_tactic_using_expr();

    void init_stop_at(options const & opts);

    void replace_theorem(certified_declaration const & thm);

public:
    parser(environment const & env, io_state const & ios,
           std::istream & strm, char const * str_name,
           bool use_exceptions = false, unsigned num_threads = 1,
           snapshot const * s = nullptr, snapshot_vector * sv = nullptr,
           info_manager * im = nullptr, keep_theorem_mode tmode = keep_theorem_mode::All);
    ~parser();

    bool ignore_noncomputable() const { return m_ignore_noncomputable; }
    void set_ignore_noncomputable() { m_ignore_noncomputable = true; }

    unsigned curr_expr_lbp() const { return curr_lbp_core(false); }
    unsigned curr_tactic_lbp() const { return curr_lbp_core(true); }

    cmd_table const & cmds() const { return get_cmd_table(env()); }

    void set_cache(definition_cache * c) { m_cache = c; }
    void cache_definition(name const & n, expr const & pre_type, expr const & pre_value,
                          level_param_names const & ls, expr const & type, expr const & value);
    /** \brief Try to find an elaborated definition for (n, pre_type, pre_value) in the cache */
    optional<std::tuple<level_param_names, expr, expr>>
    find_cached_definition(name const & n, expr const & pre_type, expr const & pre_value);
    void erase_cached_definition(name const & n) { if (m_cache) m_cache->erase(n); }

    bool are_info_lines_valid(unsigned start_line, unsigned end_line) const;
    bool collecting_info() const { return m_info_manager; }
    void remove_proof_state_info(pos_info const & start, pos_info const & end);

    void set_index(declaration_index * i) { m_index = i; }
    void add_decl_index(name const & n, pos_info const & pos, name const & k, expr const & t);
    void add_ref_index(name const & n, pos_info const & pos);
    void add_abbrev_index(name const & a, name const & d);

    environment const & env() const { return m_env; }
    io_state const & ios() const { return m_ios; }
    local_level_decls const & get_local_level_decls() const { return m_local_level_decls; }
    local_expr_decls const & get_local_expr_decls() const { return m_local_decls; }

    bool has_tactic_decls();
    expr mk_by(expr const & t, pos_info const & pos);
    expr mk_by_plus(expr const & t, pos_info const & pos);

    bool keep_new_thms() const { return m_keep_theorem_mode != keep_theorem_mode::DiscardAll; }

    void updt_options();
    options get_options() const { return m_ios.get_options(); }
    template<typename T> void set_option(name const & n, T const & v) { m_ios.set_option(n, v); }

    name mk_fresh_name() { return m_ngen.next(); }
    name_generator mk_ngen() { return m_ngen.mk_child(); }

    /** \brief Return the current position information */
    pos_info pos() const { return pos_info(m_scanner.get_line(), m_scanner.get_pos()); }
    expr save_pos(expr e, pos_info p);
    expr rec_save_pos(expr const & e, pos_info p);
    expr update_pos(expr e, pos_info p);
    pos_info pos_of(expr const & e, pos_info default_pos) const;
    pos_info pos_of(expr const & e) const { return pos_of(e, pos()); }
    pos_info cmd_pos() const { return m_last_cmd_pos; }
    name const & get_cmd_token() const { return m_cmd_token; }
    void set_line(unsigned p) { return m_scanner.set_line(p); }

    expr mk_app(expr fn, expr arg, pos_info const & p);
    expr mk_app(std::initializer_list<expr> const & args, pos_info const & p);

    unsigned num_threads() const { return m_num_threads; }
    void add_delayed_theorem(environment const & env, name const & n, level_param_names const & ls, expr const & t, expr const & v);
    void add_delayed_theorem(certified_declaration const & cd);
    environment reveal_theorems(buffer<name> const & ds);
    bool in_theorem_queue(name const & n) const { return m_theorem_queue_set.contains(n); }

    /** \brief Read the next token. */
    void scan();
    /** \brief Return the current token */
    scanner::token_kind curr() const { return m_curr; }
    /** \brief Return true iff the current token is an identifier */
    bool curr_is_identifier() const { return curr() == scanner::token_kind::Identifier; }
    /** \brief Return true iff the current token is a numeral */
    bool curr_is_numeral() const { return curr() == scanner::token_kind::Numeral; }
    /** \brief Return true iff the current token is a string */
    bool curr_is_string() const { return curr() == scanner::token_kind::String; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_keyword() const { return curr() == scanner::token_kind::Keyword; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_command() const { return curr() == scanner::token_kind::CommandKeyword; }
    /** \brief Return true iff the current token is a Lua script block */
    bool curr_is_script_block() const { return curr() == scanner::token_kind::ScriptBlock; }
    /** \brief Return true iff the current token is EOF */
    bool curr_is_eof() const { return curr() == scanner::token_kind::Eof; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_quoted_symbol() const { return curr() == scanner::token_kind::QuotedSymbol; }
    /** \brief Return true iff the current token is a keyword named \c tk or an identifier named \c tk */
    bool curr_is_token_or_id(name const & tk) const;
    /** \brief Return true iff the current token is a command, EOF, period or script block */
    bool curr_is_command_like() const;
    /** \brief Return true iff the current token is a backtick ` */
    bool curr_is_backtick() const { return curr() == scanner::token_kind::Backtick; }
    /** \brief Read the next token if the current one is not End-of-file. */
    void next() { if (m_curr != scanner::token_kind::Eof) scan(); }
    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    bool curr_is_token(name const & tk) const;
    /** \brief Check current token, and move to next characther, throw exception if current token is not \c tk. */
    void check_token_next(name const & tk, char const * msg);
    void check_token_or_id_next(name const & tk, char const * msg);
    /** \brief Check if the current token is an identifier, if it is return it and move to next token,
        otherwise throw an exception. */
    name check_id_next(char const * msg);
    /** \brief Check if the current token is an atomic identifier, if it is, return it and move to next token,
        otherwise throw an exception. */
    name check_atomic_id_next(char const * msg);
    list<name> to_constants(name const & id, char const * msg, pos_info const & p) const;
    name to_constant(name const & id, char const * msg, pos_info const & p);
    /** \brief Check if the current token is a constant, if it is, return it and move to next token, otherwise throw an exception. */
    name check_constant_next(char const * msg);

    mpq const & get_num_val() const { return m_scanner.get_num_val(); }
    name const & get_name_val() const { return m_scanner.get_name_val(); }
    std::string const & get_str_val() const { return m_scanner.get_str_val(); }
    token_info const & get_token_info() const { return m_scanner.get_token_info(); }
    std::string const & get_stream_name() const { return m_scanner.get_stream_name(); }

    io_state_stream regular_stream() const { return regular(env(), ios()); }
    io_state_stream diagnostic_stream() const { return diagnostic(env(), ios()); }

    unsigned get_small_nat();
    unsigned parse_small_nat();
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
    expr id_to_expr(name const & id, pos_info const & p);

    expr parse_expr(unsigned rbp = 0);
    /** \brief Parse an (optionally) qualified expression.
        If the input is of the form <id> : <expr>, then return the pair (some(id), expr).
        Otherwise, parse the next expression and return (none, expr).
    */
    pair<optional<name>, expr> parse_qualified_expr(unsigned rbp = 0);
    /** \brief If the input is of the form <id> := <expr>, then return the pair (some(id), expr).
        Otherwise, parse the next expression and return (none, expr).
    */
    pair<optional<name>, expr> parse_optional_assignment(unsigned rbp = 0);

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
    expr parse_tactic_expr_arg(unsigned rbp = 0);
    expr parse_tactic_id_arg();

    struct local_scope { parser & m_p; environment m_env;
        local_scope(parser & p, bool save_options = false);
        local_scope(parser & p, environment const & env);
        local_scope(parser & p, optional<environment> const & env);
        ~local_scope();
    };
    bool has_locals() const { return !m_local_decls.empty() || !m_local_level_decls.empty(); }
    void add_local_level(name const & n, level const & l, bool is_variable = false);
    void add_local_expr(name const & n, expr const & p, bool is_variable = false);
    environment add_local_ref(environment const & env, name const & n, expr const & ref);
    void add_parameter(name const & n, expr const & p);
    void add_local(expr const & p) { return add_local_expr(local_pp_name(p), p); }
    bool has_params() const { return m_has_params; }
    bool is_local_decl(expr const & l) const { return is_local(l) && m_local_decls.contains(local_pp_name(l)); }
    bool is_local_level_variable(name const & n) const { return m_level_variables.contains(n); }
    bool is_local_variable(name const & n) const { return m_variables.contains(n); }
    bool is_local_variable(expr const & e) const { return is_local_variable(local_pp_name(e)); }
    /** \brief Return true iff n is the name of a variable or parameter. */
    bool is_local_variable_parameter(name const & n) const {
        unsigned idx = m_local_decls.find_idx(n);
        return 0 < idx && idx <= m_local_decls_size_at_beg_cmd;
    }
    /** \brief Update binder information for the section parameter n, return true if success, and false if n is not a section parameter. */
    bool update_local_binder_info(name const & n, binder_info const & bi);
    void include_variable(name const & n) { m_include_vars.insert(n); }
    void omit_variable(name const & n) { m_include_vars.erase(n); }
    bool is_include_variable(name const & n) const { return m_include_vars.contains(n); }
    void get_include_variables(buffer<expr> & vars) const;
    /** \brief Position of the local level declaration named \c n in the sequence of local level decls. */
    unsigned get_local_level_index(name const & n) const;
    /** \brief Position of the local declaration named \c n in the sequence of local decls. */
    unsigned get_local_index(name const & n) const;
    unsigned get_local_index(expr const & e) const { return get_local_index(local_pp_name(e)); }
    /** \brief Return the local parameter named \c n */
    expr const * get_local(name const & n) const { return m_local_decls.find(n); }
    /** \brief Return local declarations as a list of local constants. */
    list<expr> locals_to_context() const;
    /** \brief Return all local declarations and aliases */
    list<pair<name, expr>> const & get_local_entries() const { return m_local_decls.get_entries(); }
    /** \brief Return all local level declarations */
    list<pair<name, level>> const & get_local_level_entries() const { return m_local_level_decls.get_entries(); }
    /** \brief By default, when the parser finds a unknown identifier, it signs an error.
        These scope objects temporarily change this behavior. In any scope where this object
        is declared, the parse creates a constant/local even when the identifier is unknown.
        This behavior is useful when we are trying to parse mutually recursive declarations and
        tactics.
    */
    struct undef_id_to_const_scope : public flet<undef_id_behavior> { undef_id_to_const_scope(parser & p); };
    struct undef_id_to_local_scope : public flet<undef_id_behavior> { undef_id_to_local_scope(parser &); };

    /** \brief Return the size of the stack of undefined local constants */
    unsigned get_num_undef_ids() const { return m_undef_ids.size(); }
    /** \brief Return the i-th undefined local constants */
    expr const & get_undef_id(unsigned i) const { return m_undef_ids[i]; }

    /** \brief Elaborate \c e, and tolerate metavariables in the result. */
    std::tuple<expr, level_param_names> elaborate_relaxed(expr const & e, list<expr> const & ctx = list<expr>());
    std::tuple<expr, level_param_names> elaborate(expr const & e, list<expr> const & ctx = list<expr>());
    /** \brief Elaborate \c e, and ensure it is a type. */
    std::tuple<expr, level_param_names> elaborate_type(expr const & e, list<expr> const & ctx = list<expr>(),
                                                       bool clear_pre_info = true);
    /** \brief Elaborate \c e in the given environment. */
    std::tuple<expr, level_param_names> elaborate_at(environment const & env, expr const & e);
    /** \brief Elaborate \c e (making sure the result does not have metavariables). */
    std::tuple<expr, level_param_names> elaborate(expr const & e) { return elaborate_at(m_env, e); }
    /** \brief Elaborate the definition n : t := v */
    std::tuple<expr, expr, level_param_names> elaborate_definition(name const & n, expr const & t, expr const & v);
    /** \brief Elaborate the definition n : t := v in the given environment*/
    std::tuple<expr, expr, level_param_names> elaborate_definition_at(environment const & env, local_level_decls const & lls,
                                                                      name const & n, expr const & t, expr const & v);

    expr mk_sorry(pos_info const & p);
    bool used_sorry() const { return m_used_sorry; }
    void declare_sorry();

    parser_pos_provider get_pos_provider() const { return parser_pos_provider(m_pos_table, get_stream_name(), m_last_cmd_pos); }
    void display_information_pos(pos_info p);
    void display_warning_pos(pos_info p);

    /** return true iff profiling is enabled */
    bool profiling() const { return m_profile; }

    /** parse all commands in the input stream */
    bool operator()() { return parse_commands(); }

    class in_notation_ctx {
        scanner::in_notation_ctx m_ctx;
    public:
        in_notation_ctx(parser & p):m_ctx(p.m_scanner) {}
    };
};

bool parse_commands(environment & env, io_state & ios, std::istream & in, char const * strm_name,
                    bool use_exceptions, unsigned num_threads, definition_cache * cache = nullptr,
                    declaration_index * index = nullptr, keep_theorem_mode tmode = keep_theorem_mode::All);
bool parse_commands(environment & env, io_state & ios, char const * fname, bool use_exceptions, unsigned num_threads,
                    definition_cache * cache = nullptr, declaration_index * index = nullptr,
                    keep_theorem_mode tmode = keep_theorem_mode::All);

void initialize_parser();
void finalize_parser();
}

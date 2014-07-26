/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include "util/script_state.h"
#include "util/name_map.h"
#include "util/exception.h"
#include "util/thread_script_state.h"
#include "util/script_exception.h"
#include "util/worker_queue.h"
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/expr_maps.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/kernel_bindings.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/parser_pos_provider.h"
#include "frontends/lean/theorem_queue.h"

namespace lean {
/** \brief Exception used to track parsing erros, it does not leak outside of this class. */
struct parser_error : public exception {
    pos_info m_pos;
    parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
    parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
    virtual exception * clone() const { return new parser_error(m_msg.c_str(), m_pos); }
    virtual void rethrow() const { throw *this; }
};

struct interrupt_parser {};
typedef local_decls<expr>   local_expr_decls;
typedef local_decls<level>  local_level_decls;
typedef environment         local_environment;

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
    pos_info                m_last_cmd_pos;
    pos_info                m_last_script_pos;
    unsigned                m_next_tag_idx;
    bool                    m_found_errors;
    pos_info_table_ptr      m_pos_table;
    // By default, when the parser finds a unknown identifier, it signs an error.
    // When the following flag is true, it creates a constant.
    // This flag is when we are trying to parse mutually recursive declarations.
    bool                    m_no_undef_id_error;
    optional<bool>          m_has_num;
    optional<bool>          m_has_string;
    optional<bool>          m_has_tactic_decls;
    // We process theorems in parallel
    theorem_queue           m_theorem_queue;

    void display_error_pos(unsigned line, unsigned pos);
    void display_error_pos(pos_info p);
    void display_error(char const * msg, unsigned line, unsigned pos);
    void display_error(char const * msg, pos_info p);
    void display_error(exception const & ex);
    void throw_parser_exception(char const * msg, pos_info p);
    void throw_nested_exception(exception & ex, pos_info p);

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
    expr propagate_levels(expr const & e, levels const & ls);

    cmd_table const & cmds() const { return get_cmd_table(env()); }
    parse_table const & nud() const { return get_nud_table(env()); }
    parse_table const & led() const { return get_led_table(env()); }

    unsigned curr_level_lbp() const;
    level parse_max_imax(bool is_max);
    level parse_level_id();
    level parse_level_nud();
    level parse_level_led(level left);

    void parse_imports();
    void parse_command();
    void parse_script(bool as_expr = false);
    bool parse_commands();
    unsigned curr_lbp() const;
    expr parse_notation(parse_table t, expr * left);
    expr parse_nud_notation();
    expr parse_led_notation(expr left);
    expr parse_nud();
    expr parse_id();
    expr parse_numeral_expr();
    expr parse_decimal_expr();
    expr parse_string_expr();
    expr parse_binder_core(binder_info const & bi);
    void parse_binder_block(buffer<expr> & r, binder_info const & bi);
    void parse_binders_core(buffer<expr> & r);

    friend environment section_cmd(parser & p);
    friend environment end_scoped_cmd(parser & p);

    void push_local_scope();
    void pop_local_scope();

public:
    parser(environment const & env, io_state const & ios,
           std::istream & strm, char const * str_name,
           bool use_exceptions = false, unsigned num_threads = 1,
           local_level_decls const & lds = local_level_decls(),
           local_expr_decls const & eds = local_expr_decls(),
           unsigned line = 1);
    ~parser();

    environment const & env() const { return m_env; }
    io_state const & ios() const { return m_ios; }
    local_level_decls const & get_local_level_decls() const { return m_local_level_decls; }
    local_expr_decls const & get_local_expr_decls() const { return m_local_decls; }

    bool has_tactic_decls();
    expr mk_by(expr const & t, pos_info const & pos);

    void updt_options();
    template<typename T> void set_option(name const & n, T const & v) { m_ios.set_option(n, v); }

    name mk_fresh_name() { return m_ngen.next(); }
    name_generator mk_ngen() { return m_ngen.mk_child(); }

    /** \brief Return the current position information */
    pos_info pos() const { return pos_info(m_scanner.get_line(), m_scanner.get_pos()); }
    expr save_pos(expr e, pos_info p);
    expr rec_save_pos(expr const & e, pos_info p);
    pos_info pos_of(expr const & e, pos_info default_pos);
    pos_info pos_of(expr const & e) { return pos_of(e, pos()); }
    pos_info cmd_pos() const { return m_last_cmd_pos; }
    void set_line(unsigned p) { return m_scanner.set_line(p); }

    expr mk_app(expr fn, expr arg, pos_info const & p);
    expr mk_app(std::initializer_list<expr> const & args, pos_info const & p);

    unsigned num_threads() const { return m_num_threads; }
    void add_delayed_theorem(environment const & env, name const & n, level_param_names const & ls, expr const & t, expr const & v);

    /** \brief Read the next token. */
    void scan() { m_curr = m_scanner.scan(m_env); }
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
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_quoted_symbol() const { return curr() == scanner::token_kind::QuotedSymbol; }
    /** \brief Return true if the current token is a keyword named \c tk or an identifier named \c tk */
    bool curr_is_token_or_id(name const & tk) const;
    /** \brief Read the next token if the current one is not End-of-file. */
    void next() { if (m_curr != scanner::token_kind::Eof) scan(); }
    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    bool curr_is_token(name const & tk) const;
    /** \brief Check current token, and move to next characther, throw exception if current token is not \c tk. */
    void check_token_next(name const & tk, char const * msg);
    /** \brief Check if the current token is an identifier, if it is return it and move to next token, otherwise throw an exception. */
    name check_id_next(char const * msg);
    /** \brief Check if the current token is an atomic identifier, if it is, return it and move to next token, otherwise throw an exception. */
    name check_atomic_id_next(char const * msg);
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

    bool parse_local_notation_decl();

    level parse_level(unsigned rbp = 0);

    expr parse_binder();
    local_environment parse_binders(buffer<expr> & r);
    optional<binder_info> parse_optional_binder_info();
    binder_info parse_binder_info();
    void parse_close_binder_info(optional<binder_info> const & bi);
    void parse_close_binder_info(binder_info const & bi) { return parse_close_binder_info(optional<binder_info>(bi)); }

    /** \brief Convert an identifier into an expression (constant or local constant) based on the current scope */
    expr id_to_expr(name const & id, pos_info const & p);

    expr parse_expr(unsigned rbp = 0);
    expr parse_led(expr left);
    expr parse_scoped_expr(unsigned num_params, expr const * ps, local_environment const & lenv, unsigned rbp = 0);
    expr parse_scoped_expr(buffer<expr> & ps, local_environment const & lenv, unsigned rbp = 0) {
        return parse_scoped_expr(ps.size(), ps.data(), lenv, rbp);
    }
    expr parse_scoped_expr(unsigned num_params, expr const * ps, unsigned rbp = 0) {
        return parse_scoped_expr(num_params, ps, local_environment(m_env), rbp);
    }
    expr parse_scoped_expr(buffer<expr> & ps, unsigned rbp = 0) { return parse_scoped_expr(ps.size(), ps.data(), rbp); }

    struct local_scope { parser & m_p; environment m_env; local_scope(parser & p); ~local_scope(); };
    void add_local_level(name const & n, level const & l);
    void add_local_expr(name const & n, expr const & p);
    void add_local(expr const & p) { return add_local_expr(local_pp_name(p), p); }
    /** \brief Position of the local level declaration named \c n in the sequence of local level decls. */
    unsigned get_local_level_index(name const & n) const;
    /** \brief Position of the local declaration named \c n in the sequence of local decls. */
    unsigned get_local_index(name const & n) const;
    /** \brief Return the local parameter named \c n */
    expr const * get_local(name const & n) const { return m_local_decls.find(n); }

    /**
        \brief By default, when the parser finds a unknown identifier, it signs an error.
        This scope object temporarily changes this behavior. In any scope where this object
        is declared, the parse creates a constant even when the identifier is unknown.
        This behavior is useful when we are trying to parse mutually recursive declarations.
    */
    struct no_undef_id_error_scope { parser & m_p; bool m_old; no_undef_id_error_scope(parser &); ~no_undef_id_error_scope(); };

    /** \brief Elaborate \c e, and tolerate metavariables in the result. */
    std::tuple<expr, level_param_names> elaborate_relaxed(expr const & e, list<expr> const & ctx = list<expr>());
    /** \brief Elaborate \c e, and ensure it is a type. */
    std::tuple<expr, level_param_names> elaborate_type(expr const & e, list<expr> const & ctx = list<expr>());
    /** \brief Elaborate \c e in the given environment. */
    std::tuple<expr, level_param_names> elaborate_at(environment const & env, expr const & e);
    /** \brief Elaborate \c e (making sure the result does not have metavariables). */
    std::tuple<expr, level_param_names> elaborate(expr const & e) { return elaborate_at(m_env, e); }
    /** \brief Elaborate the definition n : t := v */
    std::tuple<expr, expr, level_param_names> elaborate_definition(name const & n, expr const & t, expr const & v);
    /** \brief Elaborate the definition n : t := v in the given environment*/
    std::tuple<expr, expr, level_param_names> elaborate_definition_at(environment const & env, local_level_decls const & lls, name const & n, expr const & t, expr const & v);

    parser_pos_provider get_pos_provider() const { return parser_pos_provider(m_pos_table, get_stream_name(), m_last_cmd_pos); }

    /** parse all commands in the input stream */
    bool operator()() { return parse_commands(); }
};

bool parse_commands(environment & env, io_state & ios, std::istream & in, char const * strm_name, bool use_exceptions, unsigned num_threads);
bool parse_commands(environment & env, io_state & ios, char const * fname, bool use_exceptions, unsigned num_threads);
}

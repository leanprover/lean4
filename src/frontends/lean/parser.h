/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include "util/scoped_map.h"
#include "util/script_state.h"
#include "util/name_map.h"
#include "util/exception.h"
#include "kernel/environment.h"
#include "kernel/expr_maps.h"
#include "library/io_state.h"
#include "library/kernel_bindings.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/parser_pos_provider.h"

namespace lean {
struct parameter {
    pos_info    m_pos;
    name        m_name;
    expr        m_type;
    binder_info m_bi;
    parameter(pos_info const & p, name const & n, expr const & t, binder_info const & bi):
        m_pos(p), m_name(n), m_type(t), m_bi(bi) {}
    parameter():m_pos(0, 0) {}
};

/** \brief Exception used to track parsing erros, it does not leak outside of this class. */
struct parser_error : public exception {
    pos_info m_pos;
    parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
    parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
    virtual exception * clone() const { return new parser_error(m_msg.c_str(), m_pos); }
    virtual void rethrow() const { throw *this; }
};

struct interrupt_parser {};

class parser {
    typedef std::pair<expr, unsigned> local_entry;
    typedef scoped_map<name, local_entry, name_hash, name_eq> local_decls;

    environment             m_env;
    io_state                m_ios;
    script_state *          m_ss;
    bool                    m_verbose;
    bool                    m_use_exceptions;
    bool                    m_show_errors;

    scanner                 m_scanner;
    scanner::token_kind     m_curr;
    local_decls             m_local_decls;
    pos_info                m_last_cmd_pos;
    pos_info                m_last_script_pos;
    unsigned                m_next_tag_idx;
    bool                    m_found_errors;
    pos_info_table_ptr      m_pos_table;

    enum class scope_kind { Scope, Namespace, Structure };
    std::vector<name>       m_namespace_prefixes;
    std::vector<scope_kind> m_scope_kinds;

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
        return m_ss->apply([&](lua_State * L) {
                set_io_state    set1(L, m_ios);
                set_environment set2(L, m_env);
                return f(L);
            });
    }

    tag get_tag(expr e);
    expr copy_with_new_pos(expr const & e, pos_info p);

    void updt_options();

    parser_config const & cfg() const { return get_parser_config(env()); }
    cmd_table const & cmds() const { return cfg().m_cmds; }
    parse_table const & nud() const { return cfg().m_nud; }
    parse_table const & led() const { return cfg().m_led; }

    void parse_command();
    void parse_script(bool as_expr = false);
    bool parse_commands();
    unsigned curr_lbp() const;
    expr parse_nud();
    expr parse_led(expr left);
    expr parse_nud_keyword();
    expr parse_led_keyword(expr left);
    expr parse_id();
    expr parse_numeral_expr();
    expr parse_decimal_expr();
    expr parse_string_expr();
    expr mk_app(expr fn, expr arg, pos_info const & p);

public:
    parser(environment const & env, io_state const & ios,
           std::istream & strm, char const * str_name,
           script_state * ss = nullptr, bool use_exceptions = false);

    environment const & env() const { return m_env; }
    io_state const & ios() const { return m_ios; }
    script_state * ss() const { return m_ss; }

    parameter parse_binder();
    void parse_binders(buffer<parameter> & r);

    expr parse_expr(unsigned rbp = 0);
    expr parse_scoped_expr(unsigned num_locals, expr const * locals, unsigned rbp = 0);

    tactic parse_tactic(unsigned rbp = 0);

    /** \brief Return the current position information */
    pos_info pos() const { return pos_info(m_scanner.get_line(), m_scanner.get_pos()); }
    expr save_pos(expr e, pos_info p);
    expr rec_save_pos(expr const & e, pos_info p);
    pos_info pos_of(expr const & e, pos_info default_pos);
    pos_info pos_of(expr const & e) { return pos_of(e, pos()); }

    /** \brief Read the next token. */
    void scan() { m_curr = m_scanner.scan(m_env); }
    /** \brief Return the current token */
    scanner::token_kind curr() const { return m_curr; }
    /** \brief Read the next token if the current one is not End-of-file. */
    void next() { if (m_curr != scanner::token_kind::Eof) scan(); }
    /** \brief Return true iff the current token is equal to \c tk */
    bool curr_is_token(name const & tk) const;

    mpq const & get_num_val() const { return m_scanner.get_num_val(); }
    name const & get_name_val() const { return m_scanner.get_name_val(); }
    std::string const & get_str_val() const { return m_scanner.get_str_val(); }
    token_info const & get_token_info() const { return m_scanner.get_token_info(); }
    std::string const & get_stream_name() const { return m_scanner.get_stream_name(); }

    /** parse all commands in the input stream */
    bool operator()() { return parse_commands(); }
};

bool parse_commands(environment & env, io_state & ios, std::istream & in, char const * strm_name,
                    script_state * S, bool use_exceptions);
bool parse_commands(environment & env, io_state & ios, char const * fname, script_state * S,
                    bool use_exceptions);
}

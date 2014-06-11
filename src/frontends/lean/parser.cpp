/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "util/script_exception.h"
#include "util/sstream.h"
#include "library/io_state_stream.h"
#include "library/parser_nested_exception.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/parser.h"

#ifndef LEAN_DEFAULT_PARSER_SHOW_ERRORS
#define LEAN_DEFAULT_PARSER_SHOW_ERRORS true
#endif

namespace lean {
// ==========================================
// Parser configuration options
static name g_parser_show_errors {"lean", "parser", "show_errors"};

RegisterBoolOption(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS, "(lean parser) display error messages in the regular output channel");

bool     get_parser_show_errors(options const & opts)  { return opts.get_bool(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS); }
// ==========================================

parser::parser(environment const & env, io_state const & ios,
               std::istream & strm, char const * strm_name,
               script_state * ss, bool use_exceptions):
    m_env(env), m_ios(ios), m_ss(ss),
    m_verbose(true), m_use_exceptions(use_exceptions),
    m_scanner(strm, strm_name), m_pos_table(std::make_shared<pos_info_table>()) {
    m_found_errors = false;
    updt_options();
    m_next_tag_idx = 0;
    m_curr = scanner::token_kind::Identifier;
    protected_call([&]() { scan(); },
                   [&]() { sync_command(); });
}

void parser::updt_options() {
    m_verbose = get_verbose(m_ios.get_options());
    m_show_errors = get_parser_show_errors(m_ios.get_options());
}

void parser::display_error_pos(unsigned line, unsigned pos) {
    regular(m_env, m_ios) << get_stream_name() << ":" << line << ":";
    if (pos != static_cast<unsigned>(-1))
        regular(m_env, m_ios) << pos << ":";
    regular(m_env, m_ios) << " error:";
}
void parser::display_error_pos(pos_info p) { display_error_pos(p.first, p.second); }

void parser::display_error(char const * msg, unsigned line, unsigned pos) {
    display_error_pos(line, pos);
    regular(m_env, m_ios) << " " << msg << endl;
}

void parser::display_error(char const * msg, pos_info p) {
    display_error(msg, p.first, p.second);
}

void parser::display_error(exception const & ex) {
    parser_pos_provider pos_provider(m_pos_table, get_stream_name(), m_last_cmd_pos);
    ::lean::display_error(regular(m_env, m_ios), &pos_provider, ex);
}

void parser::throw_parser_exception(char const * msg, pos_info p) {
    throw parser_exception(msg, get_stream_name().c_str(), p.first, p.second);
}

void parser::throw_nested_exception(exception & ex, pos_info p) {
    throw parser_nested_exception(std::shared_ptr<exception>(ex.clone()),
                                  std::make_shared<parser_pos_provider>(m_pos_table, get_stream_name(), p));
}

#define CATCH(ShowError, ThrowError)                    \
m_found_errors = true;                                  \
if (!m_use_exceptions && m_show_errors) { ShowError ; } \
sync();                                                 \
if (m_use_exceptions) { ThrowError ; }

void parser::protected_call(std::function<void()> && f, std::function<void()> && sync) {
    try {
        f();
    // } catch (tactic_cmd_error & ex) {
    //     CATCH(display_error(ex),
    //           throw parser_exception(ex.what(), m_strm_name.c_str(), ex.m_pos.first, ex.m_pos.second));
    } catch (parser_exception & ex) {
        CATCH(regular(m_env, m_ios) << ex.what() << endl,
              throw);
    } catch (parser_error & ex) {
        CATCH(display_error(ex.what(), ex.m_pos),
              throw_parser_exception(ex.what(), ex.m_pos));
    } catch (interrupted & ex) {
        reset_interrupt();
        if (m_verbose)
            regular(m_env, m_ios) << "!!!Interrupted!!!" << endl;
        sync();
        if (m_use_exceptions)
            throw;
    } catch (script_exception & ex) {
         reset_interrupt();
         CATCH(display_error(ex), throw_nested_exception(ex, m_last_script_pos));
    } catch (exception & ex) {
         reset_interrupt();
         CATCH(display_error(ex), throw_nested_exception(ex, m_last_cmd_pos));
    }
}

void parser::sync_command() {
    // Keep consuming tokens until we find a Command or End-of-file
    while (curr() != scanner::token_kind::CommandKeyword && curr() != scanner::token_kind::Eof)
        next();
}

tag parser::get_tag(expr e) {
    tag t = e.get_tag();
    if (t == nulltag) {
        t = m_next_tag_idx;
        e.set_tag(t);
        m_next_tag_idx++;
    }
    return t;
}

void parser::save_pos(expr e, pos_info p) {
    m_pos_table->insert(mk_pair(get_tag(e), p));
}

bool parser::curr_is_token(name const & tk) const {
    return
        (curr() == scanner::token_kind::Keyword || curr() == scanner::token_kind::CommandKeyword) &&
        get_token_info().value() == tk;
}

static name g_period(".");

expr parser::parse_expr(unsigned /* rbp */) {
    // TODO(Leo):
    return expr();
}

expr parser::parse_scoped_expr(unsigned num_locals, expr const * locals, unsigned rbp) {
    local_decls::mk_scope scope(m_local_decls);
    for (unsigned i = 0; i < num_locals; i++) {
        lean_assert(is_local(locals[i]));
        m_local_decls.insert(local_pp_name(locals[i]), local_entry(locals[i], m_local_decls.size()));
    }
    return parse_expr(rbp);
}

tactic parser::parse_tactic(unsigned /* rbp */) {
    // TODO(Leo):
    return tactic();
}

void parser::parse_command() {
    lean_assert(curr() == scanner::token_kind::CommandKeyword);
    name const & cmd_name = get_token_info().value();
    if (auto it = cmds().find(cmd_name)) {
        next();
        m_env = it->get_fn()(*this);
    } else {
        auto p = pos();
        next();
        throw parser_error(sstream() << "unknown command '" << cmd_name << "'", p);
    }
}

void parser::parse_script(bool as_expr) {
    m_last_script_pos = pos();
    if (!m_ss)
        throw exception("failed to execute Lua script, parser does not have a Lua interpreter");
    std::string script_code = m_scanner.get_str_val();
    if (as_expr)
        script_code = "return " + script_code;
    next();
    using_script([&](lua_State * L) {
            dostring(L, script_code.c_str());
        });
}

bool parser::parse_commands() {
    try {
        bool done = false;
        while (!done) {
            protected_call([&]() {
                    check_interrupted();
                    switch (curr()) {
                    case scanner::token_kind::CommandKeyword:
                        parse_command();
                        break;
                    case scanner::token_kind::ScriptBlock:
                        parse_script();
                        break;
                    case scanner::token_kind::Eof:
                        done = true;
                        break;
                    case scanner::token_kind::Keyword:
                        if (curr_is_token(g_period)) {
                            next();
                            break;
                        }
                    default:
                        throw parser_error("command expected", pos());
                    }
                },
                [&]() { sync_command(); });
        }
    } catch (interrupt_parser) {}
    return !m_found_errors;
}


bool parse_commands(environment & env, io_state & ios, std::istream & in, char const * strm_name, script_state * S, bool use_exceptions) {
    parser p(env, ios, in, strm_name, S, use_exceptions);
    bool r = p();
    ios = p.ios();
    env = p.env();
    return r;
}

bool parse_commands(environment & env, io_state & ios, char const * fname, script_state * S, bool use_exceptions) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");
    return parse_commands(env, ios, in, fname, S, use_exceptions);
}
}

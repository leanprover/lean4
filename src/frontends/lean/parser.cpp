/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/script_exception.h"
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
}

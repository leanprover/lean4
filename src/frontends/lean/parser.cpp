/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <limits>
#include "util/interrupt.h"
#include "util/script_exception.h"
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "library/io_state_stream.h"
#include "library/parser_nested_exception.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/choice.h"
#include "library/deep_copy.h"
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

expr parser::save_pos(expr e, pos_info p) {
    m_pos_table->insert(mk_pair(get_tag(e), p));
    return e;
}

expr parser::rec_save_pos(expr const & e, pos_info p) {
    unsigned m = std::numeric_limits<unsigned>::max();
    pos_info dummy(m, 0);
    for_each(e, [&](expr const & e, unsigned) {
            if (pos_of(e, dummy).first == m) {
                save_pos(e, p);
                return true;
            }  else {
                return false;
            }
        });
    return e;
}

/** \brief Create a copy of \c e, and the position of new expression with p */
expr parser::copy_with_new_pos(expr const & e, pos_info p) {
    return rec_save_pos(deep_copy(e), p);
}

pos_info parser::pos_of(expr const & e, pos_info default_pos) {
    auto it = m_pos_table->find(get_tag(e));
    if (it == m_pos_table->end())
        return default_pos;
    else
        return it->second;
}

bool parser::curr_is_token(name const & tk) const {
    return
        (curr() == scanner::token_kind::Keyword || curr() == scanner::token_kind::CommandKeyword) &&
        get_token_info().value() == tk;
}

expr parser::mk_app(expr fn, expr arg, pos_info const & p) {
    return save_pos(::lean::mk_app(fn, arg), p);
}

// expr parser::copy_expr(expr const & e, pos_info const & p) {
//     return replace(e, [](
// }

expr parser::parse_nud_keyword() {
    // TODO(Leo)
    return expr();
}

expr parser::parse_led_keyword(expr /* left */) {
    // TODO(Leo)
    return expr();
}
expr parser::parse_id() {
    auto p  = pos();
    name id = get_name_val();
    next();
    auto it1 = m_local_decls.find(id);
    // locals
    if (it1 != m_local_decls.end())
        return copy_with_new_pos(it1->second.first, p);
    // globals
    if (m_env.find(id))
        return save_pos(mk_constant(id), p);
    // private globals
    if (auto prv_id = user_to_hidden_name(m_env, id))
        return save_pos(mk_constant(*prv_id), p);
    // aliases
    auto as = get_aliases(m_env, id);
    if (!is_nil(as)) {
        buffer<expr> new_as;
        for (auto const & e : as)
            new_as.push_back(copy_with_new_pos(e, p));
        return mk_choice(new_as.size(), new_as.data());
    }
    throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
}

expr parser::parse_numeral_expr() {
    // TODO(Leo)
    return expr();
}

expr parser::parse_decimal_expr() {
    // TODO(Leo)
    return expr();
}

expr parser::parse_string_expr() {
    // TODO(Leo)
    return expr();
}

expr parser::parse_nud() {
    switch (curr()) {
    case scanner::token_kind::Keyword:     return parse_nud_keyword();
    case scanner::token_kind::Identifier:  return parse_id();
    case scanner::token_kind::Numeral:     return parse_numeral_expr();
    case scanner::token_kind::Decimal:     return parse_decimal_expr();
    case scanner::token_kind::String:      return parse_string_expr();
    default: throw parser_error("invalid expression, unexpected token", pos());
    }
}

expr parser::parse_led(expr left) {
    switch (curr()) {
    case scanner::token_kind::Keyword:     return parse_led_keyword(left);
    case scanner::token_kind::Identifier:  return mk_app(left, parse_id(), pos_of(left));
    case scanner::token_kind::Numeral:     return mk_app(left, parse_numeral_expr(), pos_of(left));
    case scanner::token_kind::Decimal:     return mk_app(left, parse_decimal_expr(), pos_of(left));
    case scanner::token_kind::String:      return mk_app(left, parse_string_expr(), pos_of(left));
    default:                               return left;
    }
}

unsigned parser::curr_lbp() const {
    if (curr() == scanner::token_kind::Keyword)
        return get_token_info().precedence();
    else
        return 0;
}

expr parser::parse_expr(unsigned rbp) {
    expr left = parse_nud();
    while (rbp < curr_lbp()) {
        left = parse_led(left);
    }
    return left;
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

static name g_period(".");
bool parser::parse_commands() {
    // We disable hash-consing while parsing to make sure the pos-info are correct.
    scoped_expr_caching disable(false);
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

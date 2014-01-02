/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include <vector>
#include "frontends/lean/parser_imp.h"
#include "frontends/lean/parser_macros.h"

#ifndef LEAN_DEFAULT_PARSER_SHOW_ERRORS
#define LEAN_DEFAULT_PARSER_SHOW_ERRORS true
#endif

#ifndef LEAN_DEFAULT_PARSER_VERBOSE
#define LEAN_DEFAULT_PARSER_VERBOSE true
#endif

namespace lean {
// ==========================================
// Parser configuration options
static name g_parser_verbose     {"lean", "parser", "verbose"};
static name g_parser_show_errors {"lean", "parser", "show_errors"};

RegisterBoolOption(g_parser_verbose,  LEAN_DEFAULT_PARSER_VERBOSE, "(lean parser) disable/enable parser verbose messages");
RegisterBoolOption(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS, "(lean parser) display error messages in the regular output channel");

bool     get_parser_verbose(options const & opts)      { return opts.get_bool(g_parser_verbose, LEAN_DEFAULT_PARSER_VERBOSE); }
bool     get_parser_show_errors(options const & opts)  { return opts.get_bool(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS); }
// ==========================================

void parser_imp::code_with_callbacks(std::function<void()> && f) {
    m_script_state->apply([&](lua_State * L) {
            set_io_state    set1(L, m_io_state);
            set_environment set2(L, m_env);
            m_script_state->exec_unprotected([&]() {
                    f();
                });
        });
}

parser_imp::mk_scope::mk_scope(parser_imp & fn):
    m_fn(fn),
    m_scope(fn.m_local_decls),
    m_old_num_local_decls(fn.m_num_local_decls) {
}

parser_imp::mk_scope::~mk_scope() {
    m_fn.m_num_local_decls = m_old_num_local_decls;
}

pos_info parser_imp::pos_of(expr const & e, pos_info default_pos) {
    auto it = m_expr_pos_info.find(e);
    if (it == m_expr_pos_info.end())
        return default_pos;
    else
        return it->second;
}

void parser_imp::check_next(scanner::token t, char const * msg) {
    if (curr() == t)
        next();
    else
        throw parser_error(msg, pos());
}

/**
   \brief Throws a parser error if the current token is not a
   string. If it is, move to the next token.
*/
std::string parser_imp::check_string_next(char const * msg) {
    if (curr() != scanner::token::StringVal)
        throw parser_error(msg, pos());
    std::string r = curr_string();
    next();
    return r;
}

unsigned parser_imp::parse_unsigned(char const * msg) {
    lean_assert(curr_is_nat());
    mpz pval = curr_num().get_numerator();
    if (!pval.is_unsigned_int()) {
        throw parser_error(msg, pos());
    } else {
        unsigned r = pval.get_unsigned_int();
        next();
        return r;
    }
}

double parser_imp::parse_double() {
    return 0.0;
}

[[ noreturn ]] void parser_imp::not_implemented_yet() {
    // TODO(Leo)
    throw parser_error("not implemented yet", pos());
}

void parser_imp::updt_options() {
    m_verbose = get_parser_verbose(m_io_state.get_options());
    m_show_errors = get_parser_show_errors(m_io_state.get_options());
}

/**
   \brief Parse a block of Lua code. If as_expr is true, then
   it appends the string "return " in front of the script.
*/
void parser_imp::parse_script(bool as_expr) {
    m_last_script_pos = mk_pair(m_scanner.get_script_block_line(), m_scanner.get_script_block_pos());
    if (!m_script_state)
        throw exception("failed to execute Lua script, parser does not have a Lua interpreter");
    std::string script_code = m_scanner.get_str_val();
    if (as_expr) {
        script_code = "return " + script_code;
    }
    next();
    using_script([&](lua_State * L) {
            dostring(L, script_code.c_str());
        });
}

void parser_imp::parse_script_expr() { return parse_script(true); }

parser_imp::parser_imp(environment const & env, io_state const & st, std::istream & in,
                       script_state * S, bool use_exceptions, bool interactive):
    m_env(env),
    m_io_state(st),
    m_scanner(in),
    m_elaborator(env),
    m_use_exceptions(use_exceptions),
    m_interactive(interactive),
    m_script_state(S),
    m_set_parser(m_script_state, this) {
    m_namespace_prefixes.push_back(name());
    m_check_identifiers = true;
    updt_options();
    m_found_errors = false;
    m_num_local_decls = 0;
    m_scanner.set_command_keywords(get_command_keywords());
    if (m_script_state) {
        m_script_state->apply([&](lua_State * L) {
                m_expr_macros   = &get_expr_macros(L);
                m_tactic_macros = &get_tactic_macros(L);
                m_cmd_macros    = &get_cmd_macros(L);
                for (auto const & p : *m_cmd_macros) {
                    m_scanner.add_command_keyword(p.first);
                }
            });
    } else {
        m_expr_macros   = nullptr;
        m_tactic_macros = nullptr;
        m_cmd_macros    = nullptr;
    }
    scan();
}

void parser_imp::show_prompt(bool interactive, io_state const & ios) {
    if (interactive) {
        regular(ios) << "# ";
        regular(ios).flush();
    }
}

void parser_imp::show_prompt() {
    show_prompt(m_interactive, m_io_state);
}

void parser_imp::show_tactic_prompt() {
    if (m_interactive) {
        regular(m_io_state) << "## ";
        regular(m_io_state).flush();
    }
}

/** \brief Parse a sequence of commands. This method also perform error management. */
bool parser_imp::parse_commands() {
    bool done = false;
    while (!done) {
        protected_call([&]() {
                check_interrupted();
                switch (curr()) {
                case scanner::token::CommandId:   if (!parse_command()) done = true; break;
                case scanner::token::ScriptBlock: parse_script(); break;
                case scanner::token::Period:      show_prompt(); next(); break;
                case scanner::token::Eof:         done = true; break;
                default:
                    throw parser_error("Command expected", pos());
                }
            }, [&]() {
                // Keep consuming tokens until we find a Command or End-of-file
                show_prompt();
                while (curr() != scanner::token::CommandId && curr() != scanner::token::Eof && curr() != scanner::token::Period)
                    next();
                if (curr_is_period())
                    next();
            });
    }
    return !m_found_errors;
}

/** \brief Parse an expression. */
expr parser_imp::parse_expr_main() {
    try {
        auto p = m_elaborator(parse_expr());
        check_no_metavar(p, "invalid expression, it still contains metavariables after elaboration");
        return p.first;
    } catch (parser_error & ex) {
        throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
    }
}
};

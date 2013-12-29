/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_READLINE
#include <stdio.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <stdlib.h>
#include <unistd.h>
#include <algorithm>
#endif
#include <utility>
#include <string>
#include <tuple>
#include <vector>
#include <limits>
#include "util/flet.h"
#include "util/luaref.h"
#include "util/scoped_map.h"
#include "util/exception.h"
#include "util/sstream.h"
#include "util/script_state.h"
#include "util/script_exception.h"
#include "util/interrupt.h"
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/normalizer.h"
#include "kernel/type_checker.h"
#include "kernel/free_vars.h"
#include "kernel/builtin.h"
#include "kernel/kernel_exception.h"
#include "kernel/expr_maps.h"
#include "kernel/printer.h"
#include "kernel/metavar.h"
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "kernel/type_checker_justification.h"
#include "library/expr_lt.h"
#include "library/arith/arith.h"
#include "library/io_state.h"
#include "library/placeholder.h"
#include "library/kernel_bindings.h"
#include "library/elaborator/elaborator_exception.h"
#include "library/tactic/proof_state.h"
#include "library/tactic/tactic.h"
#include "library/tactic/apply_tactic.h"
#include "library/elaborator/elaborator.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/frontend_elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/notation.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/environment_scope.h"

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

// ==========================================
// Builtin commands
static name g_definition_kwd("Definition");
static name g_variable_kwd("Variable");
static name g_variables_kwd("Variables");
static name g_theorem_kwd("Theorem");
static name g_axiom_kwd("Axiom");
static name g_universe_kwd("Universe");
static name g_eval_kwd("Eval");
static name g_show_kwd("Show");
static name g_check_kwd("Check");
static name g_infix_kwd("Infix");
static name g_infixl_kwd("Infixl");
static name g_infixr_kwd("Infixr");
static name g_notation_kwd("Notation");
static name g_echo_kwd("Echo");
static name g_set_kwd("SetOption");
static name g_options_kwd("Options");
static name g_env_kwd("Environment");
static name g_import_kwd("Import");
static name g_help_kwd("Help");
static name g_coercion_kwd("Coercion");
static name g_exit_kwd("Exit");
static name g_push_kwd("Push");
static name g_pop_kwd("Pop");
static name g_scope_kwd("Scope");
static name g_end_scope_kwd("EndScope");
static name g_apply("apply");
static name g_done("done");
static name g_back("back");
static name g_abort("abort");
static name g_assumption("assumption");
static list<name> g_tactic_cmds = { g_apply, g_done, g_back, g_abort, g_assumption };
/** \brief Table/List with all builtin command keywords */
static list<name> g_command_keywords = {g_definition_kwd, g_variable_kwd, g_variables_kwd, g_theorem_kwd, g_axiom_kwd, g_universe_kwd, g_eval_kwd,
                                        g_show_kwd, g_check_kwd, g_infix_kwd, g_infixl_kwd, g_infixr_kwd, g_notation_kwd, g_echo_kwd,
                                        g_set_kwd, g_env_kwd, g_options_kwd, g_import_kwd, g_help_kwd, g_coercion_kwd, g_exit_kwd, g_push_kwd,
                                        g_pop_kwd, g_scope_kwd, g_end_scope_kwd};
// ==========================================

// ==========================================
// Support for parsing levels
static name g_max_name("max");
static name g_cup_name("\u2294");
static name g_plus_name("+");
static unsigned g_level_plus_prec = 10;
static unsigned g_level_cup_prec  = 5;
// ==========================================

// A name that can't be created by the user.
// It is used as placeholder for parsing A -> B expressions which
// are syntax sugar for (Pi (_ : A), B)
static name g_unused = name::mk_internal_unique_name();

enum class macro_arg_kind { Expr, Exprs, Bindings, Id, Int, String, Comma, Assign, Tactic, Tactics };
struct macro {
    list<macro_arg_kind> m_arg_kinds;
    luaref               m_fn;
    unsigned             m_precedence;
    macro(list<macro_arg_kind> const & as, luaref const & fn, unsigned prec):m_arg_kinds(as), m_fn(fn), m_precedence(prec) {}
};
typedef name_map<macro> macros;
macros & get_expr_macros(lua_State * L);
macros & get_tactic_macros(lua_State * L);
macros & get_cmd_macros(lua_State * L);

static char g_set_parser_key;

/** \brief Return a reference to the parser object */
parser::imp * get_parser(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_set_parser_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (lua_islightuserdata(L, -1)) {
        auto r = static_cast<parser::imp*>(lua_touserdata(L, -1));
        lua_pop(L, 1);
        return r;
    }
    lua_pop(L, 1);
    return nullptr;
}

/** \brief Auxiliary object that stores a reference to the parser object inside the Lua State */
struct set_parser {
    script_state * m_state;
    parser::imp *  m_prev;
    set_parser(script_state * S, parser::imp * ptr) {
        m_state = S;
        if (m_state) {
            m_state->apply([&](lua_State * L) {
                    m_prev  = get_parser(L);
                    lua_pushlightuserdata(L, static_cast<void *>(&g_set_parser_key));
                    lua_pushlightuserdata(L, ptr);
                    lua_settable(L, LUA_REGISTRYINDEX);
                });
        }
    }
    ~set_parser() {
        if (m_state) {
            m_state->apply([&](lua_State * L) {
                    lua_pushlightuserdata(L, static_cast<void *>(&g_set_parser_key));
                    lua_pushlightuserdata(L, m_prev);
                    lua_settable(L, LUA_REGISTRYINDEX);
                });
        }
    }
};

/**
    \brief Actual implementation for the parser functional object

    \remark It is an instance of a Pratt parser
    (http://en.wikipedia.org/wiki/Pratt_parser) described in the paper
    "Top down operator precedence". This algorithm is super simple,
    and it is easy to support user-defined infix/prefix/postfix/mixfix
    operators.
*/
class parser::imp {
    friend class parser;
    friend int mk_cmd_macro(lua_State * L);
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef name_map<expr> builtins;
    typedef std::pair<unsigned, unsigned> pos_info;
    typedef expr_map<pos_info> expr_pos_info;
    typedef expr_map<tactic>   tactic_hints; // a mapping from placeholder to tactic
    typedef buffer<std::tuple<pos_info, name, expr, bool>> bindings_buffer;
    environment         m_env;
    io_state            m_io_state;
    scanner             m_scanner;
    frontend_elaborator m_elaborator;
    macros const *      m_expr_macros;
    macros const *      m_cmd_macros;
    macros const *      m_tactic_macros;
    scanner::token      m_curr;
    bool                m_use_exceptions;
    bool                m_interactive;
    bool                m_found_errors;
    local_decls         m_local_decls;
    unsigned            m_num_local_decls;
    expr_pos_info       m_expr_pos_info;
    pos_info            m_last_cmd_pos;
    pos_info            m_last_script_pos;
    tactic_hints        m_tactic_hints;
    // If true then return error when parsing identifiers and it is not local or global.
    // We set this flag off when parsing tactics. The apply_tac may reference
    // a hypothesis in the proof state. This hypothesis is not visible until we
    // execute the tactic.
    bool                m_check_identifiers;

    script_state *      m_script_state;
    set_parser          m_set_parser;

    bool                m_verbose;
    bool                m_show_errors;

    /** \brief Exception used to track parsing erros, it does not leak outside of this class. */
    struct parser_error : public exception {
        pos_info m_pos;
        parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
        parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
        virtual exception * clone() const { return new parser_error(m_msg.c_str(), m_pos); }
        virtual void rethrow() const { throw *this; }
    };

    struct tactic_cmd_error : public parser_error {
        proof_state m_state;
        tactic_cmd_error(char const * msg, pos_info const & p, proof_state const & s):parser_error(msg, p), m_state(s) {}
        tactic_cmd_error(sstream const & msg, pos_info const & p, proof_state const & s):parser_error(msg, p), m_state(s) {}
        virtual exception * clone() const { return new tactic_cmd_error(m_msg.c_str(), m_pos, m_state); }
        virtual void rethrow() const { throw *this; }
    };

    struct metavar_not_synthesized_exception : public exception {
        context m_mvar_ctx;
        expr    m_mvar;
        expr    m_mvar_type;
    public:
        metavar_not_synthesized_exception(context const & ctx, expr const & mvar, expr const & mvar_type, char const * msg):
            exception(msg), m_mvar_ctx(ctx), m_mvar(mvar), m_mvar_type(mvar_type) {}
    };

    template<typename F>
    typename std::result_of<F(lua_State * L)>::type using_script(F && f) {
        return m_script_state->apply([&](lua_State * L) {
                set_io_state    set1(L, m_io_state);
                set_environment set2(L, m_env);
                return f(L);
            });
    }

    template<typename F>
    void code_with_callbacks(F && f) {
        m_script_state->apply([&](lua_State * L) {
                set_io_state    set1(L, m_io_state);
                set_environment set2(L, m_env);
                m_script_state->exec_unprotected([&]() {
                        f();
                    });
            });
    }

    /**
        \brief Auxiliar struct for creating/destroying a new scope for
        local declarations.
    */
    struct mk_scope {
        imp &                 m_fn;
        local_decls::mk_scope m_scope;
        unsigned              m_old_num_local_decls;
        mk_scope(imp & fn):
            m_fn(fn),
            m_scope(fn.m_local_decls),
            m_old_num_local_decls(fn.m_num_local_decls) {
        }
        ~mk_scope() {
            m_fn.m_num_local_decls = m_old_num_local_decls;
        }
    };

    /** \brief Return the current position information */
    pos_info pos() const { return mk_pair(m_scanner.get_line(), m_scanner.get_pos()); }

    /** \brief Return the position associated with \c e. If there is none, then return \c default_pos. */
    pos_info pos_of(expr const & e, pos_info default_pos) {
        auto it = m_expr_pos_info.find(e);
        if (it == m_expr_pos_info.end())
            return default_pos;
        else
            return it->second;
    }

    /** \brief Associate position \c p with \c e and return \c e */
    expr save(expr const & e, pos_info p) { m_expr_pos_info[e] = p; return e; }

    /** \brief Read the next token. */
    void scan() { m_curr = m_scanner.scan(); }
    /** \brief Return the current token */
    scanner::token curr() const { return m_curr; }
    /** \brief Read the next token if the current one is not End-of-file. */
    void next() { if (m_curr != scanner::token::Eof) scan(); }

    /** \brief Return the name associated with the current token. */
    name const & curr_name() const { return m_scanner.get_name_val(); }
    /** \brief Return the numeral associated with the current token. */
    mpq const & curr_num() const { return m_scanner.get_num_val(); }
    /** \brief Return the string associated with the current token. */
    std::string const & curr_string() const { return m_scanner.get_str_val(); }

    /**
        \brief Check if the current token is \c t, and move to the
        next one. If the current token is not \c t, it throws a parser error.
    */
    void check_next(scanner::token t, char const * msg) {
        if (curr() == t)
            next();
        else
            throw parser_error(msg, pos());
    }

    /** \brief Return true iff the current token is an identifier */
    bool curr_is_identifier() const { return curr() == scanner::token::Id; }
    /** \brief Return true iff the current token is a '_" */
    bool curr_is_placeholder() const { return curr() == scanner::token::Placeholder; }
    /** \brief Return true iff the current token is a natural number */
    bool curr_is_nat() const { return curr() == scanner::token::NatVal; }
    /** \brief Return true iff the current token is a '(' */
    bool curr_is_lparen() const { return curr() == scanner::token::LeftParen; }
    /** \brief Return true iff the current token is a '{' */
    bool curr_is_lcurly() const { return curr() == scanner::token::LeftCurlyBracket; }
    /** \brief Return true iff the current token is a ':' */
    bool curr_is_colon() const { return curr() == scanner::token::Colon; }
    /** \brief Return true iff the current token is a ',' */
    bool curr_is_comma() const { return curr() == scanner::token::Comma; }
    /** \brief Return true iff the current token is a ':=' */
    bool curr_is_assign() const { return curr() == scanner::token::Assign; }
    /** \brief Return true iff the current token is an 'in' token */
    bool curr_is_in() const { return curr() == scanner::token::In; }
    /** \brief Return true iff the current token is '.' */
    bool curr_is_period() const { return curr() == scanner::token::Period; }
    /** \brief Return true iff the current token is a tactic command */
    bool curr_is_tactic_cmd() const {
        return curr_is_identifier() && std::find(g_tactic_cmds.begin(), g_tactic_cmds.end(), curr_name()) != g_tactic_cmds.end();
    }

    /** \brief Throws a parser error if the current token is not an identifier. */
    void check_identifier(char const * msg) { if (!curr_is_identifier()) throw parser_error(msg, pos()); }
    /**
        \brief Throws a parser error if the current token is not an
        identifier. If it is, move to the next token.
    */
    name check_identifier_next(char const * msg) { check_identifier(msg); name r = curr_name(); next(); return r; }
    /** \brief Throws a parser error if the current token is not '_'. If it is, move to the next token. */
    void check_placeholder_next(char const * msg) { check_next(scanner::token::Placeholder, msg); }
    /** \brief Throws a parser error if the current token is not ':'. If it is, move to the next token. */
    void check_colon_next(char const * msg) { check_next(scanner::token::Colon, msg); }
    /** \brief Throws a parser error if the current token is not ','. If it is, move to the next token. */
    void check_comma_next(char const * msg) { check_next(scanner::token::Comma, msg); }
    /** \brief Throws a parser error if the current token is not ')'. If it is, move to the next token. */
    void check_rparen_next(char const * msg) { check_next(scanner::token::RightParen, msg); }
    /** \brief Throws a parser error if the current token is not '}'. If it is, move to the next token. */
    void check_rcurly_next(char const * msg) { check_next(scanner::token::RightCurlyBracket, msg); }
    /** \brief Throws a parser error if the current token is not ':='. If it is, move to the next token. */
    void check_assign_next(char const * msg) { check_next(scanner::token::Assign, msg); }
    /** \brief Throws a parser error if the current token is not '.'. If it is, move to the next token. */
    void check_period_next(char const * msg) { check_next(scanner::token::Period, msg); }

    /**
        \brief Throws a parser error if the current token is not a
        string. If it is, move to the next token.
    */
    std::string check_string_next(char const * msg) {
        if (curr() != scanner::token::StringVal)
            throw parser_error(msg, pos());
        std::string r = curr_string();
        next();
        return r;
    }

    /**
       @name Error handling
    */

    /*@{*/
    void display_error_pos(unsigned line, unsigned pos) {
        regular(m_io_state) << "Error (line: " << line;
        if (pos != static_cast<unsigned>(-1))
            regular(m_io_state) << ", pos: " << pos;
        regular(m_io_state) << ")";
    }

    void display_error_pos(pos_info const & p) { display_error_pos(p.first, p.second); }

    void display_error_pos(optional<expr> const & e) {
        if (e) {
            auto it = m_expr_pos_info.find(*e);
            if (it == m_expr_pos_info.end())
                return display_error_pos(m_last_cmd_pos);
            else
                return display_error_pos(it->second);
        } else {
            return display_error_pos(m_last_cmd_pos);
        }
    }

    void display_error(char const * msg, unsigned line, unsigned pos) {
        display_error_pos(line, pos);
        regular(m_io_state) << " " << msg << endl;
    }

    void display_error(char const * msg) {
        display_error(msg, m_scanner.get_line(), m_scanner.get_pos());
    }

    void display_error(kernel_exception const & ex) {
        optional<expr> main_expr = ex.get_main_expr();
        if (main_expr)
            display_error_pos(some_expr(m_elaborator.get_original(*main_expr)));
        else
            display_error_pos(main_expr);
        regular(m_io_state) << " " << ex << endl;
    }

    void display_error(metavar_not_synthesized_exception const & ex) {
        display_error_pos(some_expr(m_elaborator.get_original(ex.m_mvar)));
        regular(m_io_state) << " " << ex.what() << ", metavariable: " << ex.m_mvar << ", type:\n";
        formatter fmt = m_io_state.get_formatter();
        options opts  = m_io_state.get_options();
        regular(m_io_state) << mk_pair(fmt(ex.m_mvar_ctx, ex.m_mvar_type, true, opts), opts) << "\n";
    }

    struct lean_pos_info_provider : public pos_info_provider {
        imp const & m_ref;
        lean_pos_info_provider(imp const & r):m_ref(r) {}
        virtual std::pair<unsigned, unsigned> get_pos_info(expr const & e) const {
            expr const & o = m_ref.m_elaborator.get_original(e);
            auto it = m_ref.m_expr_pos_info.find(o);
            if (it == m_ref.m_expr_pos_info.end())
                throw exception("position is not available"); // information is not available
            return it->second;
        }
    };

    void display_error(elaborator_exception const & ex) {
        formatter fmt = m_io_state.get_formatter();
        options opts  = m_io_state.get_options();
        lean_pos_info_provider pos_provider(*this);
        regular(m_io_state) << mk_pair(ex.get_justification().pp(fmt, opts, &pos_provider, true), opts) << endl;
    }

    void display_error(script_exception const & ex) {
        switch (ex.get_source()) {
        case script_exception::source::String:
            display_error_pos(ex.get_line() + m_last_script_pos.first - 1, static_cast<unsigned>(-1));
            regular(m_io_state) << " executing script," << ex.get_msg() << endl;
            break;
        case script_exception::source::File:
            display_error_pos(m_last_script_pos);
            regular(m_io_state) << " executing external script (" << ex.get_filename() << ":" << ex.get_line() << ")," << ex.get_msg() << endl;
            break;
        case script_exception::source::Unknown:
            display_error_pos(m_last_script_pos);
            regular(m_io_state) << " executing script, exact error position is not available, " << ex.what() << endl;
            break;
        }
    }

    void display_error(tactic_cmd_error const & ex) {
        display_error(ex.what(), ex.m_pos.first, ex.m_pos.second);
        display_proof_state(ex.m_state);
    }

    /**
       \brief Execute the given function \c f, and handle exceptions occurring
       when executing \c f.
       The parameter \c s is an error synchronization procedure.
    */
    template<typename F, typename Sync>
    void protected_call(F && f, Sync && sync) {
        try {
            f();
        } catch (tactic_cmd_error & ex) {
            m_found_errors = true;
            if (m_show_errors)
                display_error(ex);
            sync();
            if (m_use_exceptions)
                throw;
        } catch (parser_error & ex) {
            m_found_errors = true;
            if (m_show_errors)
                display_error(ex.what(), ex.m_pos.first, ex.m_pos.second);
            sync();
            if (m_use_exceptions) {
                throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
            }
        } catch (kernel_exception & ex) {
            m_found_errors = true;
            if (m_show_errors)
                display_error(ex);
            sync();
            if (m_use_exceptions)
                throw;
        } catch (elaborator_exception & ex) {
            m_found_errors = true;
            if (m_show_errors)
                display_error(ex);
            sync();
            if (m_use_exceptions)
                throw;
        } catch (metavar_not_synthesized_exception & ex) {
            m_found_errors = true;
            if (m_show_errors)
                display_error(ex);
            sync();
            if (m_use_exceptions)
                throw;
        } catch (script_exception & ex) {
            m_found_errors = true;
            reset_interrupt();
            if (m_show_errors)
                display_error(ex);
            sync();
            if (m_use_exceptions)
                throw;
        } catch (interrupted & ex) {
            if (m_verbose)
                regular(m_io_state) << "!!!Interrupted!!!" << endl;
            reset_interrupt();
            sync();
            if (m_use_exceptions)
                throw;
        } catch (exception & ex) {
            m_found_errors = true;
            if (m_show_errors)
                display_error(ex.what());
            sync();
            if (m_use_exceptions)
                throw;
        }
    }
    /*@}*/

    unsigned parse_unsigned(char const * msg) {
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

    double parse_double() {
        return 0.0;
    }

    [[ noreturn ]] void not_implemented_yet() {
        // TODO(Leo)
        throw parser_error("not implemented yet", pos());
    }

    /**
       @name Parse Universe levels
    */
    /*@{*/
    level parse_level_max() {
        auto p = pos();
        next();
        buffer<level> lvls;
        while (curr_is_identifier() || curr_is_nat()) {
            lvls.push_back(parse_level());
        }
        if (lvls.size() < 2)
            throw parser_error("invalid level expression, max must have at least two arguments", p);
        level r = lvls[0];
        for (unsigned i = 1; i < lvls.size(); i++)
            r = max(r, lvls[i]);
        return r;
    }

    level parse_level_nud_id() {
        name id = curr_name();
        if (id == g_max_name) {
            return parse_level_max();
        } else {
            next();
            return m_env->get_uvar(id);
        }
    }

    level parse_level_nud_int() {
        auto p  = pos();
        mpz val = curr_num().get_numerator();
        next();
        if (!val.is_unsigned_int())
            throw parser_error("invalid level expression, value does not fit in a machine integer", p);
        return level() + val.get_unsigned_int();
    }

    level parse_level_lparen() {
        next();
        level r = parse_level();
        check_rparen_next("invalid level expression, ')' expected");
        return r;
    }

    level parse_level_nud() {
        switch (curr()) {
        case scanner::token::Id:        return parse_level_nud_id();
        case scanner::token::NatVal:    return parse_level_nud_int();
        case scanner::token::LeftParen: return parse_level_lparen();
        default:
            throw parser_error("invalid level expression", pos());
        }
    }

    level parse_level_led_plus(level const & left) {
        auto p = pos();
        next();
        level right = parse_level(g_level_plus_prec);
        if (!is_lift(right) || !lift_of(right).is_bottom())
            throw parser_error("invalid level expression, right hand side of '+' (aka universe lift operator) must be a numeral", p);
        return left + lift_offset(right);
    }

    level parse_level_led_cup(level const & left) {
        next();
        level right = parse_level(g_level_cup_prec);
        return max(left, right);
    }

    level parse_level_led(level const & left) {
        switch (curr()) {
        case scanner::token::Id:
            if (curr_name() == g_plus_name)     return parse_level_led_plus(left);
            else if (curr_name() == g_cup_name) return parse_level_led_cup(left);
        default:
            throw parser_error("invalid level expression", pos());
        }
    }

    unsigned curr_level_lbp() {
        switch (curr()) {
        case scanner::token::Id: {
            name const & id = curr_name();
            if (id == g_plus_name) return g_level_plus_prec;
            else if (id == g_cup_name) return g_level_cup_prec;
            else return 0;
        }
        default: return 0;
        }
    }

    /** \brief Parse a universe level */
    level parse_level(unsigned rbp = 0) {
        level left = parse_level_nud();
        while (rbp < curr_level_lbp()) {
            left = parse_level_led(left);
        }
        return left;
    }
    /*@}*/

    /**
       @name Parse Expressions
    */
    /*@{*/

    /**
       \brief Return the size of the implicit vector associated with the given denotation.
    */
    unsigned get_implicit_vector_size(expr const & d) {
        return get_implicit_arguments(m_env, d).size();
    }

    /**
       \brief Return a vector \c v that is the implicit vector for some \c d in \c ds,
       and <tt>v.size() == min{get_implicit_vector_size(d) | d in ds}</tt>
    */
    std::vector<bool> const & get_smallest_implicit_vector(list<expr> const & ds) {
        std::vector<bool> const * r = nullptr;
        unsigned m = std::numeric_limits<unsigned>::max();
        for (expr const & d : ds) {
            std::vector<bool> const & v = get_implicit_arguments(m_env, d);
            unsigned s = v.size();
            if (s == 0) {
                return v;
            } else if (s < m) {
                r = &v;
                m = s;
            }
        }
        lean_assert(r);
        return *r;
    }

    /**
       \brief Return <tt>min{get_implicit_vector_size(d) | d in ds}</tt>
    */
    unsigned get_smallest_implicit_vector_size(list<expr> const & ds) {
        return get_smallest_implicit_vector(ds).size();
    }

    /**
       \brief Return the function associated with the given operator.
       If the operator has been overloaded, it returns a choice expression
       of the form <tt>(choice f_1 f_2 ... f_k)</tt> where f_i's are different options.
       After we finish parsing, the elaborator
       resolve/decide which f_i should be used.
    */
    expr mk_fun(operator_info const & op, pos_info const & pos) {
        list<expr> const & fs = op.get_denotations();
        lean_assert(!is_nil(fs));
        auto it = fs.begin();
        expr r = *it;
        ++it;
        if (it == fs.end()) {
            return r;
        } else {
            unsigned min_sz = get_smallest_implicit_vector_size(fs);
            buffer<expr> alternatives;
            auto add_alternative = [&](expr const & d) {
                unsigned sz = get_implicit_vector_size(d);
                if (sz > min_sz) {
                    // must fill the difference with placeholders
                    buffer<expr> aux;
                    aux.push_back(d);
                    for (unsigned i = min_sz; i < sz; i++)
                        aux.push_back(save(mk_placeholder(), pos));
                    alternatives.push_back(mk_app(aux));
                } else {
                    alternatives.push_back(d);
                }
            };
            add_alternative(r);
            for (; it != fs.end(); ++it)
                add_alternative(*it);
            return mk_choice(alternatives.size(), alternatives.data());
        }
    }

    /**
       \brief Create an application for the given operator and
       (explicit) arguments.
    */
    expr mk_application(operator_info const & op, pos_info const & pos, unsigned num_args, expr const * args) {
        buffer<expr> new_args;
        expr f = save(mk_fun(op, pos), pos);
        new_args.push_back(f);
        // See lean_frontend.cpp for the definition of compatible denotations.
        auto imp_args = get_smallest_implicit_vector(op.get_denotations());
        unsigned i = 0;
        for (unsigned j = 0; j < imp_args.size(); j++) {
            if (imp_args[j]) {
                new_args.push_back(save(mk_placeholder(), pos));
            } else {
                if (i >= num_args)
                    throw parser_error(sstream() << "unexpected number of arguments for denotation with implicit arguments, it expects " << num_args << " explicit argument(s)", pos);
                new_args.push_back(args[i]);
                i++;
            }
        }
        for (; i < num_args; i++)
            new_args.push_back(args[i]);
        return save(mk_app(new_args), pos);
    }
    expr mk_application(operator_info const & op, pos_info const & pos, std::initializer_list<expr> const & l) {
        return mk_application(op, pos, l.size(), l.begin());
    }
    expr mk_application(operator_info const & op, pos_info const & pos, expr const & arg) {
        return mk_application(op, pos, 1, &arg);
    }
    expr mk_application(operator_info const & op, pos_info const & pos, buffer<expr> const & args) {
        return mk_application(op, pos, args.size(), args.data());
    }

    /** \brief Parse a user defined prefix operator. */
    expr parse_prefix(operator_info const & op) {
        auto p = pos();
        return mk_application(op, p, parse_expr(op.get_precedence()));
    }

    /** \brief Parse a user defined postfix operator. */
    expr parse_postfix(expr const & left, operator_info const & op) {
        return mk_application(op, pos(), left);
    }

    /** \brief Parse a user defined infix operator. */
    expr parse_infix(expr const & left, operator_info const & op) {
        auto p = pos();
        return mk_application(op, p, {left, parse_expr(op.get_precedence()+1)});
    }

    /** \brief Parse a user defined infix-left operator. */
    expr parse_infixl(expr const & left, operator_info const & op) {
        auto p = pos();
        return mk_application(op, p, {left, parse_expr(op.get_precedence())});
    }

    /** \brief Parse a user defined infix-right operator. */
    expr parse_infixr(expr const & left, operator_info const & op) {
        auto p = pos();
        return mk_application(op, p, {left, parse_expr(op.get_precedence()-1)});
    }

    /**
        \brief Throws an error if the current token is not an identifier named \c op_part.
        If it is, move to the next toke. The error message assumes
        this method has been used when parsing mixfix operators.
    */
    void check_op_part(name const & op_part) {
        if (!curr_is_identifier() || curr_name() != op_part)
            throw parser_error(sstream() << "invalid mixfix operator application, '" << op_part << "' expected", pos());
        next();
    }

    /**
        \brief Auxiliary function for #parse_mixfixl and #parse_mixfixo

        It parses (ID _)*
    */
    void parse_mixfix_args(list<name> const & ops, unsigned prec, buffer<expr> & args) {
        auto it = ops.begin();
        ++it;
        while (it != ops.end()) {
            check_op_part(*it);
            args.push_back(parse_expr(prec));
            ++it;
        }
    }

    /** \brief Parse user defined mixfixl operator. It has the form: ID _ ... ID _ */
    expr parse_mixfixl(operator_info const & op) {
        auto p = pos();
        buffer<expr> args;
        args.push_back(parse_expr(op.get_precedence()));
        parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
        return mk_application(op, p, args);
    }

    /** \brief Parse user defined mixfixr operator. It has the form: _ ID ... _ ID */
    expr parse_mixfixr(expr const & left, operator_info const & op) {
        auto p = pos();
        buffer<expr> args;
        args.push_back(left);
        auto parts = op.get_op_name_parts();
        auto it = parts.begin();
        ++it;
        while (it != parts.end()) {
            args.push_back(parse_expr(op.get_precedence()));
            check_op_part(*it);
            ++it;
        }
        return mk_application(op, p, args);
    }

    /** \brief Parse user defined mixfixr operator. It has the form: _ ID ... _ ID _ */
    expr parse_mixfixo(expr const & left, operator_info const & op) {
        auto p = pos();
        buffer<expr> args;
        args.push_back(left);
        args.push_back(parse_expr(op.get_precedence()));
        parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
        return mk_application(op, p, args);
    }

    /** \brief Parse user defined mixfixc operator. It has the form: ID _ ID ... _ ID */
    expr parse_mixfixc(operator_info const & op) {
        auto p = pos();
        buffer<expr> args;
        args.push_back(parse_expr(op.get_precedence()));
        list<name> const & ops = op.get_op_name_parts();
        auto it = ops.begin();
        ++it;
        while (true) {
            check_op_part(*it);
            ++it;
            if (it == ops.end())
                return mk_application(op, p, args);
            args.push_back(parse_expr(op.get_precedence()));
        }
    }

    /**
       \brief Try to find an object (Definition or Postulate) named \c
       id in the frontend/environment. If there isn't one, then tries
       to check if \c id is a builtin symbol. If it is not throws an error.
    */
    expr get_name_ref(name const & id, pos_info const & p) {
        optional<object> obj = m_env->find_object(id);
        if (obj) {
            object_kind k      = obj->kind();
            if (k == object_kind::Definition || k == object_kind::Postulate || k == object_kind::Builtin) {
                if (has_implicit_arguments(m_env, obj->get_name())) {
                    std::vector<bool> const & imp_args = get_implicit_arguments(m_env, obj->get_name());
                    buffer<expr> args;
                    pos_info p = pos();
                    expr f = (k == object_kind::Builtin) ? obj->get_value() : mk_constant(obj->get_name());
                    args.push_back(save(f, p));
                    for (unsigned i = 0; i < imp_args.size(); i++) {
                        if (imp_args[i]) {
                            args.push_back(save(mk_placeholder(), pos()));
                        } else {
                            args.push_back(parse_expr(g_app_precedence));
                        }
                    }
                    return mk_app(args);
                } else if (k == object_kind::Builtin) {
                    return obj->get_value();
                } else {
                    return mk_constant(obj->get_name());
                }
            } else {
                throw parser_error(sstream() << "invalid object reference, object '" << id << "' is not an expression.", p);
            }
        } else if (!m_check_identifiers) {
            return mk_constant(id);
        } else {
            throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
        }
    }

    void propagate_position(expr const & e, pos_info p) {
        for_each(e, [&](expr const & e, unsigned) {
                if (m_expr_pos_info.find(e) == m_expr_pos_info.end()) {
                    save(e, p);
                    return true;
                } else {
                    return false; // do not search children...
                }
            });
    }

    bool is_curr_begin_expr() const {
        switch (curr()) {
        case scanner::token::RightParen:
        case scanner::token::RightCurlyBracket:
        case scanner::token::Colon:
        case scanner::token::Comma:
        case scanner::token::Period:
        case scanner::token::CommandId:
        case scanner::token::Eof:
        case scanner::token::ScriptBlock:
        case scanner::token::In:
            return false;
        default:
            return true;
        }
    }

    bool is_curr_begin_tactic() const {
        switch (curr()) {
        case scanner::token::LeftParen: case scanner::token::Id:    return true;
        default:                                                    return false;
        }
    }

    typedef buffer<std::pair<macro_arg_kind, void*>> macro_arg_stack;
    struct macro_result {
        optional<expr>    m_expr;
        optional<tactic>  m_tactic;
        macro_result(expr const & e):m_expr(e) {}
        macro_result(tactic const & t):m_tactic(t) {}
        macro_result() {}
    };

    /**
       \brief Parse a macro implemented in Lua
    */
    macro_result parse_macro(list<macro_arg_kind> const & arg_kinds, luaref const & fn, unsigned prec, macro_arg_stack & args,
                             pos_info const & p) {
        if (arg_kinds) {
            auto k = head(arg_kinds);
            switch (k) {
            case macro_arg_kind::Expr: {
                expr e = parse_expr(prec);
                args.emplace_back(k, &e);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            }
            case macro_arg_kind::Exprs: {
                buffer<expr> exprs;
                while (is_curr_begin_expr()) {
                    exprs.push_back(parse_expr(prec));
                }
                args.emplace_back(k, &exprs);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            }
            case macro_arg_kind::Bindings: {
                mk_scope scope(*this);
                bindings_buffer bindings;
                parse_expr_bindings(bindings);
                args.emplace_back(k, &bindings);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            }
            case macro_arg_kind::Comma:
                check_comma_next("invalid macro, ',' expected");
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            case macro_arg_kind::Assign:
                check_comma_next("invalid macro, ':=' expected");
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            case macro_arg_kind::String: {
                std::string str = check_string_next("invalid macro, string expected");
                args.emplace_back(k, &str);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            }
            case macro_arg_kind::Int: {
                unsigned i = parse_unsigned("invalid macro argument, value does not fit in a machine integer");
                args.emplace_back(k, &i);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
             }
            case macro_arg_kind::Id: {
                name n = curr_name();
                next();
                args.emplace_back(k, &n);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            }
            case macro_arg_kind::Tactic: {
                tactic t = parse_tactic_expr();
                args.emplace_back(k, &t);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            }
            case macro_arg_kind::Tactics: {
                buffer<tactic> tactics;
                while (is_curr_begin_tactic()) {
                    tactics.push_back(parse_tactic_expr());
                }
                args.emplace_back(k, &tactics);
                return parse_macro(tail(arg_kinds), fn, prec, args, p);
            }}
            lean_unreachable();
        } else {
            // All arguments have been parsed, then call Lua procedure fn.
            m_last_script_pos = p;
            return using_script([&](lua_State * L) {
                    fn.push();
                    push_environment(L, m_env);
                    for (auto p : args) {
                        macro_arg_kind k = p.first;
                        void * arg       = p.second;
                        switch (k) {
                        case macro_arg_kind::Expr:
                            push_expr(L, *static_cast<expr*>(arg));
                            break;
                        case macro_arg_kind::Exprs: {
                            auto const & exprs = *static_cast<buffer<expr>*>(arg);
                            lua_newtable(L);
                            int i = 1;
                            for (auto e : exprs) {
                                push_expr(L, e);
                                lua_rawseti(L, -2, i);
                                i = i + 1;
                            }
                            break;
                        }
                        case macro_arg_kind::Bindings: {
                            bindings_buffer const & bindings = *static_cast<bindings_buffer*>(arg);
                            lua_newtable(L);
                            int i = 1;
                            for (auto const & b : bindings) {
                                lua_newtable(L);
                                push_name(L, std::get<1>(b));
                                lua_rawseti(L, -2, 1);
                                push_expr(L, std::get<2>(b));
                                lua_rawseti(L, -2, 2);
                                lua_rawseti(L, -2, i);
                                i = i + 1;
                            }
                            break;
                        }
                        case macro_arg_kind::Id:
                            push_name(L, *static_cast<name*>(arg));
                            break;
                        case macro_arg_kind::String:
                            lua_pushstring(L, static_cast<std::string*>(arg)->c_str());
                            break;
                        case macro_arg_kind::Int:
                            lua_pushinteger(L, *static_cast<unsigned*>(arg));
                            break;
                        case macro_arg_kind::Tactic:
                            push_tactic(L, *static_cast<tactic*>(arg));
                            break;
                        case macro_arg_kind::Tactics: {
                            auto const & tactics = *static_cast<buffer<tactic>*>(arg);
                            lua_newtable(L);
                            int i = 1;
                            for (auto t : tactics) {
                                push_tactic(L, t);
                                lua_rawseti(L, -2, i);
                                i = i + 1;
                            }
                            break;
                        }
                        default:
                            lean_unreachable();
                        }
                    }
                    pcall(L, args.size() + 1, 1, 0);
                    if (is_expr(L, -1)) {
                        expr r = to_expr(L, -1);
                        lua_pop(L, 1);
                        propagate_position(r, p);
                        return macro_result(r);
                    } else if (is_tactic(L, -1)) {
                        tactic t = to_tactic(L, -1);
                        lua_pop(L, 1);
                        return macro_result(t);
                    } else {
                        lua_pop(L, 1);
                        return macro_result();
                    }
                });
        }
    }

    expr parse_expr_macro(name const & id, pos_info const & p) {
        lean_assert(m_expr_macros && m_expr_macros->find(id) != m_expr_macros->end());
        auto m = m_expr_macros->find(id)->second;
        macro_arg_stack args;
        auto r = parse_macro(m.m_arg_kinds, m.m_fn, m.m_precedence, args, p);
        if (r.m_expr) {
            return *(r.m_expr);
        } else {
            throw parser_error("failed to execute macro, unexpected result type", p);
        }
    }

    /**
        \brief Parse an identifier that has a "null denotation" (See
        paper: "Top down operator precedence"). A nud identifier is a
        token that appears at the beginning of a language construct.
        In Lean, local declarations (i.e., local functions), user
        defined prefix, mixfixl and mixfixc operators, and global
        functions can begin a language construct.
    */
    expr parse_nud_id() {
        auto p = pos();
        name id = curr_name();
        next();
        auto it = m_local_decls.find(id);
        if (it != m_local_decls.end()) {
            return save(mk_var(m_num_local_decls - it->second - 1), p);
        } else if (m_expr_macros && m_expr_macros->find(id) != m_expr_macros->end()) {
            return parse_expr_macro(id, p);
        } else {
            operator_info op = find_nud(m_env, id);
            if (op) {
                switch (op.get_fixity()) {
                case fixity::Prefix:  return parse_prefix(op);
                case fixity::Mixfixl: return parse_mixfixl(op);
                case fixity::Mixfixc: return parse_mixfixc(op);
                default: lean_unreachable(); // LCOV_EXCL_LINE
                }
            } else {
                return save(get_name_ref(id, p), p);
            }
        }
    }

    /**
        \brief Parse an identifier that has a "left denotation" (See
        paper: "Top down operator precedence"). A left identifier is a
        token that appears inside of a construct (to left of the rest
        of the construct). In Lean, local declarations (i.e., function
        application arguments), user defined infix, infixl, infixr,
        mixfixr and global values (as function application arguments)
        can appear inside of a construct.
    */
    expr parse_led_id(expr const & left) {
        auto p  = pos();
        auto p2 = pos_of(left, p);
        name id = curr_name();
        next();
        auto it = m_local_decls.find(id);
        if (it != m_local_decls.end()) {
            return save(mk_app(left, save(mk_var(m_num_local_decls - it->second - 1), p)), p2);
        } else if (m_expr_macros && m_expr_macros->find(id) != m_expr_macros->end()) {
            return save(mk_app(left, parse_expr_macro(id, p)), p2);
        } else {
            operator_info op = find_led(m_env, id);
            if (op) {
                switch (op.get_fixity()) {
                case fixity::Infix:   return parse_infix(left, op);
                case fixity::Infixl:  return parse_infixl(left, op);
                case fixity::Infixr:  return parse_infixr(left, op);
                case fixity::Mixfixr: return parse_mixfixr(left, op);
                case fixity::Mixfixo: return parse_mixfixo(left, op);
                case fixity::Postfix: return parse_postfix(left, op);
                default: lean_unreachable(); // LCOV_EXCL_LINE
                }
            } else {
                return save(mk_app(left, save(get_name_ref(id, p), p)), p2);
            }
        }
    }

    /** \brief Parse <tt>expr '=' expr</tt>. */
    expr parse_eq(expr const & left) {
        auto p = pos();
        next();
        expr right = parse_expr(g_eq_precedence);
        return save(mk_eq(left, right), p);
    }

    /** \brief Parse <tt>expr '->' expr</tt>. */
    expr parse_arrow(expr const & left) {
        auto p = pos();
        next();
        mk_scope scope(*this);
        register_binding(g_unused);
        // The -1 is a trick to get right associativity in Pratt's parsers
        expr right = parse_expr(g_arrow_precedence-1);
        return save(mk_arrow(left, right), p);
    }

    /** \brief Parse <tt>'(' expr ')'</tt>. */
    expr parse_lparen() {
        auto p = pos();
        next();
        expr r = curr() == scanner::token::Type ? parse_type(true) : parse_expr();
        check_rparen_next("invalid expression, ')' expected");
        return save(r, p);
    }

    /**
        \brief Parse a sequence of identifiers <tt>ID*</tt>. Store the
        result in \c result.
    */
    void parse_names(buffer<std::pair<pos_info, name>> & result) {
        while (curr_is_identifier()) {
            result.emplace_back(pos(), curr_name());
            next();
        }
    }

    /** \brief Register the name \c n as a local declaration. */
    void register_binding(name const & n) {
        unsigned lvl = m_num_local_decls;
        m_local_decls.insert(n, lvl);
        m_num_local_decls++;
        lean_assert(m_local_decls.find(n)->second == lvl);
    }

    /**
        \brief Parse <tt>ID ... ID ':' expr</tt>, where the expression
        represents the type of the identifiers.

        \remark If \c implicit_decl is true, then the bindings should be
        marked as implicit. This flag is set to true, for example,
        when we are parsing definitions such as:
        <code> Definition f {A : Type} (a b : A), A := ... </code>
        The <code>{A : Type}</code> is considered an implicit argument declaration.

        \remark If \c suppress_type is true, then the type doesn't
        need to be provided. That is, we automatically include a placeholder.
    */
    void parse_simple_bindings(bindings_buffer & result, bool implicit_decl, bool suppress_type) {
        buffer<std::pair<pos_info, name>> names;
        parse_names(names);
        optional<expr> type;
        if (!suppress_type) {
            check_colon_next("invalid binder, ':' expected");
            type = parse_expr();
        } else if (curr_is_colon()) {
            next();
            type = parse_expr();
        }
        unsigned sz = result.size();
        result.resize(sz + names.size());
        for (std::pair<pos_info, name> const & n : names) register_binding(n.second);
        unsigned i = names.size();
        while (i > 0) {
            --i;
            expr arg_type;
            if (type)
                arg_type = lift_free_vars(*type, i);
            else
                arg_type = save(mk_placeholder(), names[i].first);
            result[sz + i] = std::make_tuple(names[i].first, names[i].second, arg_type, implicit_decl);
        }
    }

    /**
        \brief Parse a sequence of <tt>'(' ID ... ID ':' expr ')'</tt>.

        This is used when parsing lambda, Pi, forall/exists expressions and
        definitions.

        \remark If implicit_decls is true, then we allow declarations
        with curly braces. These declarations are used to tag implicit
        arguments. Such as:
        <code> Definition f {A : Type} (a b : A) : A := ... </code>

        \see parse_simple_bindings
    */
    void parse_bindings(bindings_buffer & result, bool implicit_decls, bool suppress_type) {
        if (curr_is_identifier()) {
            parse_simple_bindings(result, false, suppress_type);
        } else {
            // (ID ... ID : type) ... (ID ... ID : type)
            if (implicit_decls) {
                if (!curr_is_lparen() && !curr_is_lcurly())
                    throw parser_error("invalid binder, '(', '{' or identifier expected", pos());
            } else {
                if (!curr_is_lparen())
                    throw parser_error("invalid binder, '(' or identifier expected", pos());
            }
            bool implicit = curr_is_lcurly();
            next();
            parse_simple_bindings(result, implicit, suppress_type);
            if (!implicit)
                check_rparen_next("invalid binder, ')' expected");
            else
                check_rcurly_next("invalid binder, '}' expected");
            while (curr_is_lparen() || (implicit_decls && curr_is_lcurly())) {
                bool implicit = curr_is_lcurly();
                next();
                parse_simple_bindings(result, implicit, suppress_type);
                if (!implicit)
                    check_rparen_next("invalid binder, ')' expected");
                else
                    check_rcurly_next("invalid binder, '}' expected");
            }
        }
    }

    /** \brief Parse bindings for expressions such as: lambda, pi, forall, exists */
    void parse_expr_bindings(bindings_buffer & result) {
        parse_bindings(result, false, true);
    }

    /** \brief Parse bindings for object such as: axioms, variables ... */
    void parse_var_decl_bindings(bindings_buffer & result) {
        parse_bindings(result, true, false);
    }

    /** \brief Parse bindings for object such as: theorems, definitions ... */
    void parse_definition_bindings(bindings_buffer & result) {
        parse_bindings(result, true, true);
    }

    /**
        \brief Create a lambda/Pi abstraction, using the giving binders
        and body.
    */
    expr mk_abstraction(bool is_lambda, bindings_buffer const & bindings, expr const & body) {
        expr result = body;
        unsigned i = bindings.size();
        while (i > 0) {
            --i;
            pos_info p = std::get<0>(bindings[i]);
            if (is_lambda)
                result = save(mk_lambda(std::get<1>(bindings[i]), std::get<2>(bindings[i]), result), p);
            else
                result = save(mk_pi(std::get<1>(bindings[i]), std::get<2>(bindings[i]), result), p);
        }
        return result;
    }

    /** \brief Parse lambda/Pi abstraction. */
    expr parse_abstraction(bool is_lambda) {
        next();
        mk_scope scope(*this);
        bindings_buffer bindings;
        parse_expr_bindings(bindings);
        check_comma_next("invalid abstraction, ',' expected");
        expr result = parse_expr();
        return mk_abstraction(is_lambda, bindings, result);
    }

    /** \brief Parse lambda abstraction. */
    expr parse_lambda() {
        return parse_abstraction(true);
    }

    /** \brief Parse Pi abstraction. */
    expr parse_pi() {
        return parse_abstraction(false);
    }

    /** \brief Parse forall/exists */
    expr parse_quantifier(bool is_forall) {
        next();
        mk_scope scope(*this);
        bindings_buffer bindings;
        parse_expr_bindings(bindings);
        check_comma_next("invalid quantifier, ',' expected");
        expr result = parse_expr();
        unsigned i = bindings.size();
        while (i > 0) {
            --i;
            pos_info p = std::get<0>(bindings[i]);
            expr lambda = save(mk_lambda(std::get<1>(bindings[i]), std::get<2>(bindings[i]), result), p);
            if (is_forall)
                result = save(mk_forall(std::get<2>(bindings[i]), lambda), p);
            else
                result = save(mk_exists(std::get<2>(bindings[i]), lambda), p);
        }
        return result;
    }

    /** \brief Parse <tt>'forall' bindings ',' expr</tt>. */
    expr parse_forall() {
        return parse_quantifier(true);
    }

    /** \brief Parse <tt>'exists' bindings ',' expr</tt>. */
    expr parse_exists() {
        return parse_quantifier(false);
    }

    /** \brief Parse Let expression. */
    expr parse_let() {
        next();
        mk_scope scope(*this);
        buffer<std::tuple<pos_info, name, optional<expr>, expr>> bindings;
        while (true) {
            auto p   = pos();
            name id  = check_identifier_next("invalid let expression, identifier expected");
            optional<expr> type;
            if (curr_is_colon()) {
                next();
                type = parse_expr();
            }
            check_assign_next("invalid let expression, ':=' expected");
            expr val = parse_expr();
            register_binding(id);
            bindings.emplace_back(p, id, type, val);
            if (curr_is_in()) {
                next();
                expr r = parse_expr();
                unsigned i = bindings.size();
                while (i > 0) {
                    --i;
                    auto p = std::get<0>(bindings[i]);
                    r = save(mk_let(std::get<1>(bindings[i]), std::get<2>(bindings[i]), std::get<3>(bindings[i]), r), p);
                }
                return r;
            } else {
                check_comma_next("invalid let expression, ',' or 'in' expected");
            }
        }
    }

    /** \brief Parse a natural number value. */
    expr parse_nat() {
        auto p = pos();
        expr r = save(mk_nat_value(m_scanner.get_num_val().get_numerator()), p);
        next();
        return r;
    }

    expr parse_decimal() {
        auto p = pos();
        expr r = save(mk_real_value(m_scanner.get_num_val()), p);
        next();
        return r;
    }

    expr parse_string() {
        // TODO(Leo)
        not_implemented_yet();
    }

    /** \brief Parse <tt>'Type'</tt> and <tt>'Type' level</tt> expressions. */
    expr parse_type(bool level_expected) {
        auto p = pos();
        next();
        if (level_expected) {
            return save(mk_type(parse_level()), p);
        } else {
            return save(Type(), p);
        }
    }

    /** \brief Parse \c _ a hole that must be filled by the elaborator. */
    expr parse_placeholder() {
        auto p = pos();
        next();
        return save(mk_placeholder(), p);
    }

    tactic parse_tactic_macro(name tac_id, pos_info const & p) {
        lean_assert(m_tactic_macros && m_tactic_macros->find(tac_id) != m_tactic_macros->end());
        next();
        auto m = m_tactic_macros->find(tac_id)->second;
        macro_arg_stack args;
        flet<bool> set(m_check_identifiers, false);
        auto r = parse_macro(m.m_arg_kinds, m.m_fn, m.m_precedence, args, p);
        if (r.m_tactic) {
            return *(r.m_tactic);
        } else {
            throw parser_error("failed to execute macro, unexpected result type, a tactic was expected", p);
        }
    }

    /** \brief Parse a tactic expression, it can be

        1) A Lua Script Block expression that returns a tactic
        2) '(' expr ')' where expr is a proof term
        3) identifier that is the name of a tactic or proof term.
    */
    tactic parse_tactic_expr() {
        auto p = pos();
        if (curr() == scanner::token::ScriptBlock) {
            parse_script_expr();
            return using_script([&](lua_State * L) {
                    try {
                        return to_tactic(L, -1);
                    } catch (...) {
                        throw parser_error("invalid script-block, it must return a tactic", p);
                    }
                });
        } else if (curr_is_identifier() && m_tactic_macros && m_tactic_macros->find(curr_name()) != m_tactic_macros->end()) {
            return parse_tactic_macro(curr_name(), p);
        } else if (curr_is_lparen()) {
            next();
            tactic r = parse_tactic_expr();
            check_rparen_next("invalid tactic, ')' expected");
            return r;
        } else {
            name n = check_identifier_next("invalid tactic, identifier, tactic macro, '(', or 'script-block' expected");
            return using_script([&](lua_State * L) {
                    lua_getglobal(L, n.to_string().c_str());
                    try {
                        if (is_tactic(L, -1)) {
                            tactic t = to_tactic(L, -1);
                            lua_pop(L, 1);
                            return t;
                        } else {
                            throw parser_error(sstream() << "invalid tactic, '" << n << "' is not a tactic in script environment", p);
                        }
                    } catch (...) {
                        lua_pop(L, 1);
                        throw parser_error(sstream() << "unknown tactic '" << n << "'", p);
                    }
                });
        }
    }

    /** \brief Parse <tt>'show' expr 'by' tactic</tt> */
    expr parse_show_expr() {
        auto p = pos();
        next();
        expr t = parse_expr();
        if (curr_is_comma()) {
            next();
            expr b = parse_expr();
            return mk_let("show-expression", t, b, Var(0));
        } else {
            check_next(scanner::token::By, "invalid 'show' expression, 'by' or ',' expected");
            tactic tac = parse_tactic_expr();
            expr r = mk_placeholder(some_expr(t));
            m_tactic_hints.insert(mk_pair(r, tac));
            return save(r, p);
        }
    }

    /** \brief Parse <tt>'by' tactic</tt> */
    expr parse_by_expr() {
        auto p = pos();
        next();
        tactic tac = parse_tactic_expr();
        expr r = mk_placeholder();
        m_tactic_hints.insert(mk_pair(r, tac));
        return save(r, p);
    }

    /**
       \brief Auxiliary method used when processing the beginning of an expression.
    */
    expr parse_nud() {
        switch (curr()) {
        case scanner::token::Id:          return parse_nud_id();
        case scanner::token::LeftParen:   return parse_lparen();
        case scanner::token::Lambda:      return parse_lambda();
        case scanner::token::Pi:          return parse_pi();
        case scanner::token::Forall:      return parse_forall();
        case scanner::token::Exists:      return parse_exists();
        case scanner::token::Let:         return parse_let();
        case scanner::token::NatVal:      return parse_nat();
        case scanner::token::DecimalVal:  return parse_decimal();
        case scanner::token::StringVal:   return parse_string();
        case scanner::token::Placeholder: return parse_placeholder();
        case scanner::token::Type:        return parse_type(false);
        case scanner::token::Show:        return parse_show_expr();
        case scanner::token::By:          return parse_by_expr();
        default:
            throw parser_error("invalid expression, unexpected token", pos());
        }
    }

    /**
       \brief Create a new application and associate position of left with the resultant expression.
    */
    expr mk_app_left(expr const & left, expr const & arg) {
        if (is_type(left))
            throw parser_error("Type is not a function, use '(Type <universe>)' for specifying a particular type universe", pos());
        auto it = m_expr_pos_info.find(left);
        lean_assert(it != m_expr_pos_info.end());
        return save(mk_app(left, arg), it->second);
    }

    /**
       \brief Auxiliary method used when processing the 'inside' of an expression.
    */
    expr parse_led(expr const & left) {
        switch (curr()) {
        case scanner::token::Id:          return parse_led_id(left);
        case scanner::token::Eq:          return parse_eq(left);
        case scanner::token::Arrow:       return parse_arrow(left);
        case scanner::token::LeftParen:   return mk_app_left(left, parse_lparen());
        case scanner::token::NatVal:      return mk_app_left(left, parse_nat());
        case scanner::token::DecimalVal:  return mk_app_left(left, parse_decimal());
        case scanner::token::StringVal:   return mk_app_left(left, parse_string());
        case scanner::token::Placeholder: return mk_app_left(left, parse_placeholder());
        case scanner::token::Type:        return mk_app_left(left, parse_type(false));
        default:                          return left;
        }
    }

    /** \brief Return the binding power of the current token (when parsing expression). */
    unsigned curr_lbp() {
        switch (curr()) {
        case scanner::token::Id: {
            name const & id = curr_name();
            auto it = m_local_decls.find(id);
            if (it != m_local_decls.end()) {
                return g_app_precedence;
            } else if (m_expr_macros && m_expr_macros->find(id) != m_expr_macros->end()) {
                return m_expr_macros->find(id)->second.m_precedence;
            } else {
                optional<unsigned> prec = get_lbp(m_env, id);
                if (prec)
                    return *prec;
                else
                    return g_app_precedence;
            }
        }
        case scanner::token::Eq : return g_eq_precedence;
        case scanner::token::Arrow : return g_arrow_precedence;
        case scanner::token::LeftParen: case scanner::token::NatVal: case scanner::token::DecimalVal:
        case scanner::token::StringVal: case scanner::token::Type: case scanner::token::Placeholder:
            return g_app_precedence;
        default:
            return 0;
        }
    }

    /** \brief Parse an expression */
    expr parse_expr(unsigned rbp = 0) {
        expr left = parse_nud();
        while (rbp < curr_lbp()) {
            left = parse_led(left);
        }
        return left;
    }
    /*@}*/

    /**
       @name Parse Commands
    */
    /*@{*/

    /**
        \brief Register implicit arguments for the definition or
        postulate named \c n. The fourth element in the tuple bindings
        is a flag indiciating whether the argument is implicit or not.
    */
    void register_implicit_arguments(name const & n, bindings_buffer & bindings) {
        bool found = false;
        buffer<bool> imp_args;
        for (unsigned i = 0; i < bindings.size(); i++) {
            imp_args.push_back(std::get<3>(bindings[i]));
            if (imp_args.back())
                found = true;
        }
        if (found)
            mark_implicit_arguments(m_env, n, imp_args.size(), imp_args.data());
    }

    void display_proof_state(proof_state s) {
        regular(m_io_state) << "Proof state:\n" << s << endl;
    }

    void display_proof_state_if_interactive(proof_state s) {
        if (m_interactive)
            display_proof_state(s);
    }

    typedef std::vector<proof_state_seq> proof_state_seq_stack;

    /**
       \brief Apply tactic \c t to state \c s.
       When \c t succeeds, it returns the head and tail of the output state sequence.
       Throws an exception if the tactic fails, and use \c p to sign the error position.
    */
    std::pair<proof_state, proof_state_seq> apply_tactic(proof_state const & s, tactic const & t, pos_info const & p) {
        proof_state_seq::maybe_pair r;
        code_with_callbacks([&]() {
                // t may have call-backs we should set ios in the script_state
                proof_state_seq seq = t(m_env, m_io_state, s);
                r = seq.pull();
            });
        if (r) {
            return mk_pair(r->first, r->second);
        } else {
            throw tactic_cmd_error("tactic failed", p, s);
        }
    }

    /**
       \brief Try to create a proof for the input state \c s.
       It basically applies the proof_builder if \c s does not contain
       any goals left. The position information is used to throw an exception
       if \c s is not a final state.

       The resultant proof must have type \c expected_type in the context \c ctx.
    */
    expr mk_proof_for(proof_state const & s, pos_info const & p, context const & ctx, expr const & expected_type) {
        if (s.is_proof_final_state()) {
            assignment a(s.get_menv().copy());
            proof_map  m;
            expr pr = s.get_proof_builder()(m, a);
            if (has_metavar(pr)) {
                // Some tactics generate metavariables that can only be instantiated by type inference elaboration.
                // Example: apply_tactic.
                metavar_env menv = s.get_menv().copy();
                buffer<unification_constraint> ucs;
                expr pr_type = type_checker(m_env).check(pr, ctx, menv, ucs);
                ucs.push_back(mk_convertible_constraint(ctx, pr_type, expected_type, mk_type_match_justification(ctx, expected_type, pr)));
                elaborator elb(m_env, menv, ucs.size(), ucs.data(), m_io_state.get_options());
                metavar_env new_menv = elb.next();
                pr = new_menv->instantiate_metavars(pr);
                if (has_metavar(pr))
                    throw exception("synthesized proof object has unsolved metavars");
            }
            return pr;
        } else {
            throw tactic_cmd_error("invalid 'done' command, proof cannot be produced from this state", p, s);
        }
    }

    /**
       \brief Execute the \c back (backtrack) tactic command.  It
       succeeds if the stack \c stack contains proof states.  When it
       succeeds, \c s is updated with the next state in the state
       sequence on the top of \c stack. The new state is also removed
       from the stack.
    */
    void back_cmd(/* inout */ proof_state_seq_stack & stack, /* inout */ proof_state & s) {
        auto p = pos();
        next();
        while (!stack.empty()) {
            check_interrupted();
            lazy_list<proof_state> seq = stack.back();
            stack.pop_back();
            proof_state_seq::maybe_pair r;
            code_with_callbacks([&]() {
                    r = seq.pull();
                });
            if (r) {
                stack.push_back(r->second);
                s = r->first;
                return;
            }
        }
        throw tactic_cmd_error("failed to backtrack", p, s);
    }

    /**
       \brief Execute the tactic.
       This command just applies the tactic to the input state \c s.
       If it succeeds, \c s is assigned to the head of the output
       state sequence produced by the tactic.  The rest/tail of the
       output state sequence is stored on the top of the stack \c
       stack.
    */
    void tactic_cmd(/* inout */ proof_state_seq_stack & stack, /* inout */ proof_state & s) {
        auto tac_pos = pos();
        tactic t = parse_tactic_expr();
        auto r = apply_tactic(s, t, tac_pos);
        s = r.first;
        stack.push_back(r.second);
    }

    /**
       \brief Execute the \c done tactic command. It succeeds if
       a proof for \c s can be built.
    */
    expr done_cmd(proof_state const & s, context const & ctx, expr const & expected_type) {
        auto p = pos();
        next();
        return mk_proof_for(s, p, ctx, expected_type);
    }

    /**
       \brief Parse tactic command sequence for solving input state \c s.

       The proof for \c s must have type \c expected_type in the context \c ctx.
    */
    expr parse_tactic_cmds(proof_state s, context const & ctx, expr const & expected_type) {
        proof_state_seq_stack stack;
        optional<expr> pr;
        enum class status { Continue, Done, Eof, Abort };
        status st = status::Continue;
        while (st == status::Continue) {
            protected_call(
                [&]() {
                    auto p = pos();
                    check_interrupted();
                    name id;
                    switch (curr()) {
                    case scanner::token::Period:
                        display_proof_state_if_interactive(s);
                        show_tactic_prompt();
                        next();
                        break;
                    case scanner::token::Eof:
                        st = status::Eof;
                        break;
                    case scanner::token::Id:
                        id = curr_name();
                        if (id == g_back) {
                            back_cmd(stack, s);
                        } else if (id == g_done) {
                            pr = done_cmd(s, ctx, expected_type);
                            if (pr)
                                st = status::Done;
                        } else if (id == g_abort) {
                            next();
                            st = status::Abort;
                        } else {
                            tactic_cmd(stack, s);
                        }
                        break;
                    case scanner::token::ScriptBlock:
                        tactic_cmd(stack, s);
                        break;
                    case scanner::token::CommandId:
                        st = status::Abort;
                        break;
                    default:
                        next();
                        throw tactic_cmd_error("invalid tactic command, identifier expected", p, s);
                    }
                },
                [&]() {
                    // Keep consuming tokens until we find a Command or End-of-file or Tactic command
                    show_tactic_prompt();
                    while (curr() != scanner::token::CommandId && curr() != scanner::token::Eof &&
                           curr() != scanner::token::Period && !curr_is_tactic_cmd())
                        next();
                    if (curr_is_period())
                        next();
                });
        }
        switch (st) {
        case status::Done:  return *pr;
        case status::Eof:   throw tactic_cmd_error("invalid tactic command, unexpected end of file", pos(), s);
        case status::Abort: throw tactic_cmd_error("failed to prove theorem, proof has been aborted", pos(), s);
        default: lean_unreachable(); // LCOV_EXCL_LINE
        }
    }

    /**
       \brief Return a 'hint' tactic (if it exists) for the given metavariable.
       If the metavariable is not associated with any hint, then return the
       null tactic. The method also returns the position of the hint.
    */
    std::pair<optional<tactic>, pos_info> get_tactic_for(expr const & mvar) {
        expr placeholder = m_elaborator.get_original(mvar);
        auto it = m_tactic_hints.find(placeholder);
        if (it != m_tactic_hints.end()) {
            return mk_pair(some_tactic(it->second), pos_of(placeholder, pos()));
        } else {
            return mk_pair(none_tactic(), pos_of(placeholder, pos()));
        }
    }

    std::pair<expr, context> get_metavar_ctx_and_type(expr const & mvar, metavar_env const & menv) {
        expr mvar_type = menv->instantiate_metavars(menv->get_type(mvar));
        buffer<context_entry> new_entries;
        for (auto e : menv->get_context(mvar)) {
            optional<expr> d = e.get_domain();
            optional<expr> b = e.get_body();
            if (d) d = menv->instantiate_metavars(*d);
            if (b) b = menv->instantiate_metavars(*b);
            if (d)
                new_entries.emplace_back(e.get_name(), *d, b);
            else
                new_entries.emplace_back(e.get_name(), d, *b);
        }
        context mvar_ctx(to_list(new_entries.begin(), new_entries.end()));
        return mk_pair(mvar_type, mvar_ctx);
    }

    /** \brief Throw an exception if \c e contains a metavariable */
    void check_no_metavar(expr const & e, metavar_env const & menv, char const * msg) {
        auto m = find(e, [](expr const & e) -> bool { return is_metavar(e); });
        if (m) {
            auto p = get_metavar_ctx_and_type(*m, menv);
            throw metavar_not_synthesized_exception(p.second, *m, p.first, msg);
        }
    }
    void check_no_metavar(std::pair<expr, metavar_env> const & p, char const * msg) {
        check_no_metavar(p.first, p.second, msg);
    }

    /**
       \brief Try to fill the 'holes' in \c val using tactics.
       The metavar_env \c menv contains the definition of the metavariables occurring in \c val.

       If a 'hole' is associated with a "hint tactic" ('show-by' and 'by' constructs),
       then this will be the tactic used to "fill" the hole. Otherwise,
       a tactic command sequence is expected in the input stream being parsed.
    */
    expr apply_tactics(expr const & val, metavar_env & menv) {
        buffer<expr> mvars;
        for_each(val, [&](expr const & e, unsigned) {
                if (is_metavar(e)) {
                    mvars.push_back(e);
                }
                return true;
            });
        std::sort(mvars.begin(), mvars.end(), [](expr const & e1, expr const & e2) { return is_lt(e1, e2, false); });
        for (auto mvar : mvars) {
            auto p = get_metavar_ctx_and_type(mvar, menv);
            expr mvar_type   = p.first;
            context mvar_ctx = p.second;
            if (has_metavar(mvar_type))
                throw metavar_not_synthesized_exception(mvar_ctx, mvar, mvar_type,
                                                        "failed to synthesize metavar, its type contains metavariables");
            try {
                proof_state s = to_proof_state(m_env, mvar_ctx, mvar_type);
                std::pair<optional<tactic>, pos_info> hint_and_pos = get_tactic_for(mvar);
                if (hint_and_pos.first) {
                    // metavariable has an associated tactic hint
                    s = apply_tactic(s, *(hint_and_pos.first), hint_and_pos.second).first;
                    menv->assign(mvar, mk_proof_for(s, hint_and_pos.second, mvar_ctx, mvar_type));
                } else {
                    if (curr_is_period()) {
                        display_proof_state_if_interactive(s);
                        show_tactic_prompt();
                        next();
                    }
                    expr mvar_val = parse_tactic_cmds(s, mvar_ctx, mvar_type);
                    menv->assign(mvar, mvar_val);
                }
            } catch (type_is_not_proposition_exception &) {
                throw metavar_not_synthesized_exception(mvar_ctx, mvar, mvar_type, "failed to synthesize metavar, its type is not a proposition");
            }
        }
        return menv->instantiate_metavars(val);
    }

    /** \brief Auxiliary method used for parsing definitions and theorems. */
    void parse_def_core(bool is_definition) {
        next();
        expr pre_type, pre_val;
        name id = check_identifier_next("invalid definition, identifier expected");
        bindings_buffer bindings;
        if (curr_is_colon()) {
            next();
            pre_type = parse_expr();
            if (!is_definition && curr_is_period()) {
                pre_val  = save(mk_placeholder(), pos());
            } else {
                check_assign_next("invalid definition, ':=' expected");
                pre_val  = parse_expr();
            }
        } else if (is_definition && curr_is_assign()) {
            auto p   = pos();
            next();
            pre_type = save(mk_placeholder(), p);
            pre_val  = parse_expr();
        } else {
            mk_scope scope(*this);
            parse_definition_bindings(bindings);
            expr type_body;
            if (curr_is_colon()) {
                next();
                type_body = parse_expr();
            } else {
                auto p = pos();
                type_body = save(mk_placeholder(), p);
            }
            pre_type  = mk_abstraction(false, bindings, type_body);
            if (!is_definition && curr_is_period()) {
                pre_val = mk_abstraction(true, bindings, mk_placeholder());
            } else {
                check_assign_next("invalid definition, ':=' expected");
                expr val_body  = parse_expr();
                pre_val   = mk_abstraction(true, bindings, val_body);
            }
        }
        auto r = m_elaborator(id, pre_type, pre_val);
        expr type = std::get<0>(r);
        expr val  = std::get<1>(r);
        metavar_env menv = std::get<2>(r);
        check_no_metavar(type, menv, "invalid definition, type still contains metavariables after elaboration");
        if (has_metavar(val)) {
            val = apply_tactics(val, menv);
        } else {
            check_no_metavar(val, menv, "invalid definition, value still contains metavariables after elaboration");
        }
        lean_assert(!has_metavar(val));
        if (is_definition) {
            m_env->add_definition(id, type, val);
            if (m_verbose)
                regular(m_io_state) << "  Defined: " << id << endl;
        } else {
            m_env->add_theorem(id, type, val);
            if (m_verbose)
                regular(m_io_state) << "  Proved: " << id << endl;
        }
        register_implicit_arguments(id, bindings);
    }

    /**
        \brief Parse a Definition. It has one of the following two forms:

        1) 'Definition' ID ':' expr ':=' expr

        2) 'Definition' ID bindings ':' expr ':=' expr
    */
    void parse_definition() {
        parse_def_core(true);
    }

    /**
        \brief Parse a Theorem. It has one of the following two forms:

        1) 'Theorem' ID ':' expr ':=' expr

        2) 'Theorem' ID bindings ':' expr ':=' expr
    */
    void parse_theorem() {
        parse_def_core(false);
    }

    /** \brief Auxiliary method for parsing Variable and axiom declarations. */
    void parse_variable_core(bool is_var) {
        next();
        name id = check_identifier_next("invalid variable/axiom declaration, identifier expected");
        bindings_buffer bindings;
        expr type;
        if (curr_is_colon()) {
            next();
            auto p = m_elaborator(parse_expr());
            check_no_metavar(p, "invalid declaration, type still contains metavariables after elaboration");
            type = p.first;
        } else {
            mk_scope scope(*this);
            parse_var_decl_bindings(bindings);
            check_colon_next("invalid variable/axiom declaration, ':' expected");
            expr type_body = parse_expr();
            auto p = m_elaborator(mk_abstraction(false, bindings, type_body));
            check_no_metavar(p, "invalid declaration, type still contains metavariables after elaboration");
            type = p.first;
        }
        if (is_var)
            m_env->add_var(id, type);
        else
            m_env->add_axiom(id, type);
        if (m_verbose)
            regular(m_io_state) << "  Assumed: " << id << endl;
        register_implicit_arguments(id, bindings);
    }

    /** \brief Parse one of the two forms:

        1) 'Variable' ID ':' type

        2) 'Variable' ID bindings ':' type
    */
    void parse_variable() {
        parse_variable_core(true);
    }

    /** \brief Parse the form:
        'Variables' ID+ ':' type
    */
    void parse_variables() {
        next();
        mk_scope scope(*this);
        bindings_buffer bindings;
        parse_simple_bindings(bindings, false, false);
        for (auto b : bindings) {
            name const & id = std::get<1>(b);
            if (m_env->find_object(id))
                throw already_declared_exception(m_env, id);
        }
        for (auto b : bindings) {
            name const & id = std::get<1>(b);
            expr const & type = std::get<2>(b);
            m_env->add_var(id, type);
            if (m_verbose)
                regular(m_io_state) << "  Assumed: " << id << endl;
        }
    }

    /** \brief Parse one of the two forms:

        1) 'Axiom' ID ':' type

        2) 'Axiom' ID bindings ':' type
    */
    void parse_axiom() {
        parse_variable_core(false);
    }

    /** \brief Parse 'Eval' expr */
    void parse_eval() {
        next();
        expr v = m_elaborator(parse_expr()).first;
        normalizer norm(m_env);
        expr r = norm(v, context(), true);
        regular(m_io_state) << r << endl;
    }

    /** \brief Return true iff \c obj is an object that should be ignored by the Show command */
    bool is_hidden_object(object const & obj) const {
        return (obj.is_definition() && is_explicit(m_env, obj.get_name())) || !supported_by_pp(obj);
    }

    /** \brief Parse
           'Show' expr
           'Show' Environment [num]
           'Show' Environment all
           'Show' Options
    */
    void parse_show() {
        next();
        if (curr() == scanner::token::CommandId) {
            name opt_id = curr_name();
            next();
            if (opt_id == g_env_kwd) {
                buffer<object> to_display;
                bool     all = false;
                unsigned end = m_env->get_num_objects(false);
                unsigned i;
                if (curr_is_nat()) {
                    i   = parse_unsigned("invalid argument, value does not fit in a machine integer");
                } else if (curr_is_identifier() && curr_name() == "all") {
                    next();
                    i   = std::numeric_limits<unsigned>::max();
                    all = true;
                } else {
                    i = std::numeric_limits<unsigned>::max();
                }
                unsigned it          = end;
                unsigned num_imports = 0;
                while (it != 0 && i != 0) {
                    --it;
                    auto obj = m_env->get_object(it, false);
                    if (is_begin_import(obj)) {
                        lean_assert(num_imports > 0);
                        num_imports--;
                    } else if (is_end_import(obj)) {
                        num_imports++;
                    } else if (is_hidden_object(obj)) {
                        // skip
                    } else if (num_imports == 0 || all) {
                        to_display.push_back(obj);
                        --i;
                    }
                }
                std::reverse(to_display.begin(), to_display.end());
                for (auto obj : to_display) {
                    regular(m_io_state) << obj << endl;
                }
            } else if (opt_id == g_options_kwd) {
                regular(m_io_state) << pp(m_io_state.get_options()) << endl;
            } else {
                throw parser_error("invalid Show command, expression, 'Options' or 'Environment' expected", m_last_cmd_pos);
            }
        } else {
            expr v = m_elaborator(parse_expr()).first;
            regular(m_io_state) << v << endl;
        }
    }

    /** \brief Parse 'Check' expr */
    void parse_check() {
        next();
        auto p = m_elaborator(parse_expr());
        check_no_metavar(p, "invalid expression, it still contains metavariables after elaboration");
        expr v = p.first;
        expr t = type_check(v, m_env);
        formatter fmt = m_io_state.get_formatter();
        options opts  = m_io_state.get_options();
        unsigned indent = get_pp_indent(opts);
        format r = group(format{fmt(v, opts), space(), colon(), nest(indent, compose(line(), fmt(t, opts)))});
        regular(m_io_state) << mk_pair(r, opts) << endl;
    }

    /** \brief Return the (optional) precedence of a user-defined operator. */
    unsigned parse_precedence() {
        if (curr_is_nat()) {
            return parse_unsigned("invalid operator definition, precedence does not fit in a machine integer");
        } else {
            return 0;
        }
    }

    /** \brief Throw an error if the current token is not an identifier. If it is, move to next token. */
    name parse_op_id() {
        return check_identifier_next("invalid operator definition, identifier expected");
    }

    /**
        \brief Parse prefix/postfix/infix/infixl/infixr user operator
        definitions. These definitions have the form:

           - fixity [Num] ID ':' ID
    */
    void parse_op(fixity fx) {
        next();
        unsigned prec = parse_precedence();
        name op_id = parse_op_id();
        check_colon_next("invalid operator definition, ':' expected");
        name name_id = check_identifier_next("invalid operator definition, identifier expected");
        expr d     = mk_constant(name_id);
        switch (fx) {
        case fixity::Infix:   add_infix(m_env, m_io_state, op_id, prec, d); break;
        case fixity::Infixl:  add_infixl(m_env, m_io_state, op_id, prec, d); break;
        case fixity::Infixr:  add_infixr(m_env, m_io_state, op_id, prec, d); break;
        default: lean_unreachable(); // LCOV_EXCL_LINE
        }
    }

    /**
       \brief Parse notation declaration unified format

       'Notation' [Num] parts ':' ID
    */
    void parse_notation_decl() {
        auto p = pos();
        next();
        unsigned prec = parse_precedence();
        bool first             = true;
        bool prev_placeholder  = false;
        bool first_placeholder = false;
        buffer<name> parts;
        while (true) {
            if (first) {
                if (curr_is_placeholder()) {
                    prev_placeholder  = true;
                    first_placeholder = true;
                    next();
                } else {
                    parts.push_back(check_identifier_next("invalid notation declaration, identifier or '_' expected"));
                    prev_placeholder  = false;
                    first_placeholder = false;
                }
                first = false;
            } else {
                if (curr_is_colon()) {
                    next();
                    if (parts.size() == 0) {
                        throw parser_error("invalid notation declaration, it must have at least one identifier", p);
                    }
                    name name_id = check_identifier_next("invalid notation declaration, identifier expected");
                    expr d     = mk_constant(name_id);
                    if (parts.size() == 1) {
                        if (first_placeholder && prev_placeholder) {
                            // infix: _ ID _
                            add_infix(m_env, m_io_state, parts[0], prec, d);
                        } else if (first_placeholder) {
                            // postfix: _ ID
                            add_postfix(m_env, m_io_state, parts[0], prec, d);
                        } else if (prev_placeholder) {
                            // prefix: ID _
                            add_prefix(m_env, m_io_state, parts[0], prec, d);
                        } else {
                            throw parser_error("invalid notation declaration, at least one placeholder expected", p);
                        }
                    } else {
                        if (first_placeholder && prev_placeholder) {
                            // mixfixo: _ ID ... ID _
                            add_mixfixo(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                        } else if (first_placeholder) {
                            // mixfixr: _ ID ... ID
                            add_mixfixr(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                        } else if (prev_placeholder) {
                            // mixfixl: ID _ ... ID _
                            add_mixfixl(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                        } else {
                            // mixfixc: ID _ ... _ ID
                            add_mixfixc(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                        }
                    }
                    return;
                } else {
                    if (prev_placeholder) {
                        parts.push_back(check_identifier_next("invalid notation declaration, identifier or ':' expected"));
                        prev_placeholder = false;
                    } else {
                        check_placeholder_next("invalid notation declaration, '_' or ':' expected");
                        prev_placeholder = true;
                    }
                }
            }
        }
    }

    /** Parse 'Echo' [string] */
    void parse_echo() {
        next();
        std::string msg = check_string_next("invalid echo command, string expected");
        regular(m_io_state) << msg << endl;
    }

    /** Parse 'SetOption' [id] [value] */
    void parse_set() {
        next();
        auto id_pos = pos();
        name id = check_identifier_next("invalid set options, identifier (i.e., option name) expected");
        auto decl_it = get_option_declarations().find(id);
        if (decl_it == get_option_declarations().end()) {
            // add "lean" prefix
            name lean_id = name("lean") + id;
            decl_it = get_option_declarations().find(lean_id);
            if (decl_it == get_option_declarations().end()) {
                throw parser_error(sstream() << "unknown option '" << id << "', type 'Help Options.' for list of available options", id_pos);
            } else {
                id = lean_id;
            }
        }
        option_kind k = decl_it->second.kind();
        switch (curr()) {
        case scanner::token::Id:
            if (k != BoolOption)
                throw parser_error(sstream() << "invalid option value, given option is not Boolean", pos());
            if (curr_name() == "true")
                m_io_state.set_option(id, true);
            else if (curr_name() == "false")
                m_io_state.set_option(id, false);
            else
                throw parser_error("invalid Boolean option value, 'true' or 'false' expected", pos());
            next();
            break;
        case scanner::token::StringVal:
            if (k != StringOption)
                throw parser_error("invalid option value, given option is not a string", pos());
            m_io_state.set_option(id, curr_string());
            next();
            break;
        case scanner::token::NatVal:
            if (k != IntOption && k != UnsignedOption)
                throw parser_error("invalid option value, given option is not an integer", pos());
            m_io_state.set_option(id, parse_unsigned("invalid option value, value does not fit in a machine integer"));
            break;
        case scanner::token::DecimalVal:
            if (k != DoubleOption)
                throw parser_error("invalid option value, given option is not floating point value", pos());
            m_io_state.set_option(id, parse_double());
            break;
        default:
            throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", pos());
        }
        updt_options();
        if (m_verbose)
            regular(m_io_state) << "  Set: " << id << endl;
    }

    bool import_lean_file(std::string const & fname) {
        std::ifstream in(fname);
        if (!in.is_open())
            throw parser_error(sstream() << "invalid import command, failed to open file '" << fname << "'", m_last_cmd_pos);
        if (!m_env->mark_imported(fname.c_str())) {
            // module already imported
            return false;
        }
        try {
            script_state state; // Empty state object for the imported module
            io_state ios = m_io_state;
            ios.set_option(g_parser_verbose, false);
            parser import_parser(m_env, ios, in, &state, true /* use exceptions */, false /* not interactive */);
            import_parser();
        } catch (interrupted &) {
            throw;
        } catch (exception &) {
            throw parser_error(sstream() << "failed to import file '" << fname << "'", m_last_cmd_pos);
        }
        return true;
    }

    void parse_import() {
        next();
        std::string fname;
        if (curr_is_identifier()) {
            fname = name_to_file(curr_name());
            next();
        } else {
            fname  = check_string_next("invalid import command, string (i.e., file name) or identifier expected");
        }
        std::string ffname = find_file(fname);
        bool r = false;
        if (is_lean_file(ffname)) {
            r = import_lean_file(ffname);
        } else if (is_lua_file(ffname)) {
            if (!m_script_state)
                throw parser_error(sstream() << "failed to import Lua file '" << fname << "', parser does not have an intepreter", m_last_cmd_pos);
            r = m_script_state->import_explicit(ffname.c_str());
        } else {
            // assume is a Lean file
            r = import_lean_file(ffname);
        }
        if (m_verbose) {
            if (r)
                regular(m_io_state) << "  Imported '" << fname << "'" << endl;
            else
                regular(m_io_state) << "  Skipped '" << fname << "'" << endl;
        }
    }

    void parse_help() {
        next();
        if (curr() == scanner::token::CommandId) {
            name opt_id = curr_name();
            next();
            if (opt_id == g_options_kwd) {
                regular(m_io_state) << "Available options:" << endl;
                for (auto p : get_option_declarations()) {
                    auto opt = p.second;
                    regular(m_io_state) << "  " << opt.get_name() << " (" << opt.kind() << ") "
                                        << opt.get_description() << " (default: " << opt.get_default_value() << ")" << endl;
                }
            } else {
                throw parser_error("invalid help command", m_last_cmd_pos);
            }
        } else {
            regular(m_io_state) << "Available commands:" << endl
                                << "  Axiom [id] : [type]    assert/postulate a new axiom" << endl
                                << "  Check [expr]           type check the given expression" << endl
                                << "  Definition [id] : [type] := [expr]   define a new element" << endl
                                << "  Echo [string]          display the given string" << endl
                                << "  EndScope               end the current scope and import its objects into the parent scope" << endl
                                << "  Eval [expr]            evaluate the given expression" << endl
                                << "  Exit                   exit" << endl
                                << "  Help                   display this message" << endl
                                << "  Help Options           display available options" << endl
                                << "  Help Notation          describe commands for defining infix, mixfix, postfix operators" << endl
                                << "  Import [string]        load the given file" << endl
                                << "  Push                   create a scope (it is just an alias for the command Scope)" << endl
                                << "  Pop                    discard the current scope" << endl
                                << "  Scope                  create a scope" << endl
                                << "  SetOption [id] [value] set option [id] with value [value]" << endl
                                << "  Show [expr]            pretty print the given expression" << endl
                                << "  Show Options           show current the set of assigned options" << endl
                                << "  Show Environment       show objects in the environment, if [Num] provided, then show only the last [Num] objects" << endl
                                << "  Show Environment [num] show the last num objects in the environment" << endl
                                << "  Theorem [id] : [type] := [expr]      define a new theorem" << endl
                                << "  Variable [id] : [type] declare/postulate an element of the given type" << endl
                                << "  Universe [id] [level]  declare a new universe variable that is >= the given level" << endl;
            #if !defined(LEAN_WINDOWS)
            regular(m_io_state) << "Type Ctrl-D to exit" << endl;
            #endif
        }
    }

    /** \brief Parse 'Coercion' expr */
    void parse_coercion() {
        next();
        expr coercion = parse_expr();
        add_coercion(m_env, coercion);
        if (m_verbose)
            regular(m_io_state) << "  Coercion " << coercion << endl;
    }

    void reset_env(environment env) {
        m_env = env;
        m_elaborator.reset(env);
        m_io_state.set_formatter(mk_pp_formatter(env));
    }

    void parse_scope() {
        next();
        reset_env(m_env->mk_child());
    }

    void parse_pop() {
        next();
        if (!m_env->has_parent())
            throw parser_error("main scope cannot be removed", m_last_cmd_pos);
        reset_env(m_env->parent());
    }

    void parse_end_scope() {
        next();
        if (!m_env->has_parent())
            throw parser_error("main scope cannot be removed", m_last_cmd_pos);
        auto new_objects = export_local_objects(m_env);
        reset_env(m_env->parent());
        for (auto const & obj : new_objects) {
            if (obj.is_theorem())
                m_env->add_theorem(obj.get_name(), obj.get_type(), obj.get_value());
            else
                m_env->add_definition(obj.get_name(), obj.get_type(), obj.get_value(), obj.is_opaque());
        }
    }

    void parse_cmd_macro(name cmd_id, pos_info const & p) {
        lean_assert(m_cmd_macros && m_cmd_macros->find(cmd_id) != m_cmd_macros->end());
        next();
        auto m = m_cmd_macros->find(cmd_id)->second;
        macro_arg_stack args;
        parse_macro(m.m_arg_kinds, m.m_fn, m.m_precedence, args, p);
    }

    /** \brief Parse a Lean command. */
    bool parse_command() {
        m_elaborator.clear();
        m_expr_pos_info.clear();
        m_tactic_hints.clear();
        m_last_cmd_pos = pos();
        name const & cmd_id = curr_name();
        if (cmd_id == g_definition_kwd) {
            parse_definition();
        } else if (cmd_id == g_variable_kwd) {
            parse_variable();
        } else if (cmd_id == g_variables_kwd) {
            parse_variables();
        } else if (cmd_id == g_theorem_kwd) {
            parse_theorem();
        } else if (cmd_id == g_axiom_kwd) {
            parse_axiom();
        } else if (cmd_id == g_eval_kwd) {
            parse_eval();
        } else if (cmd_id == g_show_kwd) {
            parse_show();
        } else if (cmd_id == g_check_kwd) {
            parse_check();
        } else if (cmd_id == g_infix_kwd) {
            parse_op(fixity::Infix);
        } else if (cmd_id == g_infixl_kwd) {
            parse_op(fixity::Infixl);
        } else if (cmd_id == g_infixr_kwd) {
            parse_op(fixity::Infixr);
        } else if (cmd_id == g_notation_kwd) {
            parse_notation_decl();
        } else if (cmd_id == g_echo_kwd) {
            parse_echo();
        } else if (cmd_id == g_set_kwd) {
            parse_set();
        } else if (cmd_id == g_import_kwd) {
            parse_import();
        } else if (cmd_id == g_help_kwd) {
            parse_help();
        } else if (cmd_id == g_coercion_kwd) {
            parse_coercion();
        } else if (cmd_id == g_exit_kwd) {
            next();
            return false;
        } else if (cmd_id == g_push_kwd || cmd_id == g_scope_kwd) {
            parse_scope();
        } else if (cmd_id == g_pop_kwd) {
            parse_pop();
        } else if (cmd_id == g_end_scope_kwd) {
            parse_end_scope();
        } else if (m_cmd_macros && m_cmd_macros->find(cmd_id) != m_cmd_macros->end()) {
            parse_cmd_macro(cmd_id, m_last_cmd_pos);
        } else {
            next();
            throw parser_error(sstream() << "invalid command '" << cmd_id << "'", m_last_cmd_pos);
        }
        return true;
    }
    /*@}*/

    void updt_options() {
        m_verbose = get_parser_verbose(m_io_state.get_options());
        m_show_errors = get_parser_show_errors(m_io_state.get_options());
    }

    /**
       \brief Parse a block of Lua code. If as_expr is true, then
       it appends the string "return " in front of the script.
    */
    void parse_script(bool as_expr = false) {
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

    void parse_script_expr() { return parse_script(true); }

public:
    imp(environment const & env, io_state const & st, std::istream & in, script_state * S, bool use_exceptions, bool interactive):
        m_env(env),
        m_io_state(st),
        m_scanner(in),
        m_elaborator(env),
        m_use_exceptions(use_exceptions),
        m_interactive(interactive),
        m_script_state(S),
        m_set_parser(m_script_state, this) {
        m_check_identifiers = true;
        updt_options();
        m_found_errors = false;
        m_num_local_decls = 0;
        m_scanner.set_command_keywords(g_command_keywords);
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

    static void show_prompt(bool interactive, io_state const & ios) {
        if (interactive) {
            regular(ios) << "# ";
            regular(ios).flush();
        }
    }

    void show_prompt() {
        show_prompt(m_interactive, m_io_state);
    }

    void show_tactic_prompt() {
        if (m_interactive) {
            regular(m_io_state) << "## ";
            regular(m_io_state).flush();
        }
    }

    /** \brief Parse a sequence of commands. This method also perform error management. */
    bool parse_commands() {
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
    expr parse_expr_main() {
        try {
            auto p = m_elaborator(parse_expr());
            check_no_metavar(p, "invalid expression, it still contains metavariables after elaboration");
            return p.first;
        } catch (parser_error & ex) {
            throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
        }
    }
};

parser::parser(environment const & env, io_state const & ios, std::istream & in, script_state * S, bool use_exceptions, bool interactive) {
    parser::imp::show_prompt(interactive, ios);
    m_ptr.reset(new imp(env, ios, in, S, use_exceptions, interactive));
}

parser::parser(environment const & env, std::istream & in, script_state * S, bool use_exceptions, bool interactive):
    parser(env, io_state(), in, S, use_exceptions, interactive) {
    m_ptr->m_io_state.set_formatter(mk_pp_formatter(m_ptr->m_env));
}

parser::~parser() {
}

bool parser::operator()() {
    return m_ptr->parse_commands();
}

expr parser::parse_expr() {
    return m_ptr->parse_expr_main();
}

io_state parser::get_io_state() const {
    return m_ptr->m_io_state;
}

#ifdef LEAN_USE_READLINE
// Hackish wrapper for implementing a streambuf on top of the readline library
class readline_streambuf : public std::streambuf {
    std::string      m_buffer;
    std::streamsize  m_curr;
    std::streamsize  m_high;
protected:
    virtual int_type underflow() {
        while (m_curr == m_high) {
            char * line = readline("");
            if (!line) {
                // EOF received
                return traits_type::eof();
            } else if (strlen(line) == 0) {
                // ignore blank line
                m_buffer.push_back('\n');
                free(line);
            } else {
                add_history(line);
                m_buffer += line;
                m_buffer.push_back('\n');
                free(line);
                m_high = m_buffer.size();
            }
        }

        return traits_type::to_int_type(m_buffer[m_curr]);
    }

    virtual int_type uflow() {
        int_type r = underflow();
        if (r != traits_type::eof())
            m_curr++;
        return r;
    }

    virtual int_type pbackfail(int_type c) {
        if (m_curr == 0)
            return traits_type::eof();
        m_curr--;
        if (c != traits_type::eof())
            m_buffer[m_curr] = c;
        return traits_type::eof() + 1; // something different from eof()
    }

    virtual std::streamsize showmanyc() {
        return m_high - m_curr;
    }

public:
    readline_streambuf():
        m_curr(0), m_high(0) {
        setbuf(0, 0);
    }
};

struct readline_config {
    FILE * m_devnull;
    readline_config() {
        // By default, the readline library echos the input in the standard output.
        // We can change this behavior by setting rl_outstream to /dev/null
        m_devnull = fopen("/dev/null", "a");
        rl_outstream = m_devnull;
    }
    ~readline_config() {
        fclose(m_devnull);
    }
};
static readline_config g_readline_config;
#endif

shell::shell(environment const & env, io_state const & ios, script_state * S):m_env(env), m_io_state(ios), m_script_state(S) {
}

shell::shell(environment const & env, script_state * S):m_env(env), m_io_state(), m_script_state(S) {
    m_io_state.set_formatter(mk_pp_formatter(m_env));
}

shell::~shell() {
}

bool shell::operator()() {
#ifdef LEAN_USE_READLINE
    readline_streambuf buf;
    std::istream is(&buf);
    parser p(m_env, m_io_state, is, m_script_state, false, true);
#else
    parser p(m_env, m_io_state, std::cin, m_script_state, false, true);
#endif
    return p();
}

bool parse_commands(environment const & env, io_state & ios, std::istream & in, script_state * S, bool use_exceptions, bool interactive) {
    parser p(env, ios, in, S, use_exceptions, interactive);
    bool r = p();
    ios = p.get_io_state();
    return r;
}

expr parse_expr(environment const & env, io_state & ios, std::istream & in, script_state * S, bool use_exceptions) {
    parser p(env, ios, in, S, use_exceptions);
    expr r = p.parse_expr();
    ios = p.get_io_state();
    return r;
}

static char g_parser_expr_macros_key;
static char g_parser_tactic_macros_key;
static char g_parser_cmd_macros_key;
DECL_UDATA(macros)

macros & get_macros(lua_State * L, char * key) {
    lua_pushlightuserdata(L, static_cast<void *>(key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (lua_isnil(L, -1)) {
        lua_pop(L, 1);
        lua_pushlightuserdata(L, static_cast<void *>(key));
        push_macros(L, macros());
        lua_settable(L, LUA_REGISTRYINDEX);
        lua_pushlightuserdata(L, static_cast<void *>(key));
        lua_gettable(L, LUA_REGISTRYINDEX);
    }
    lean_assert(is_macros(L, -1));
    macros & r = to_macros(L, -1);
    lua_pop(L, 1);
    return r;
}

macros & get_expr_macros(lua_State * L)   { return get_macros(L, &g_parser_expr_macros_key); }
macros & get_tactic_macros(lua_State * L) { return get_macros(L, &g_parser_tactic_macros_key); }
macros & get_cmd_macros(lua_State * L)    { return get_macros(L, &g_parser_cmd_macros_key); }

void mk_macro(lua_State * L, macros & mtable) {
    int nargs = lua_gettop(L);
    name macro_name = to_name_ext(L, 1);
    unsigned prec = nargs == 4 ? lua_tointeger(L, 4) : g_app_precedence;
    luaL_checktype(L, 3, LUA_TFUNCTION); // user-fun
    buffer<macro_arg_kind> arg_kind_buffer;
    int n = objlen(L, 2);
    for (int i = 1; i <= n; i++) {
        lua_rawgeti(L, 2, i);
        arg_kind_buffer.push_back(static_cast<macro_arg_kind>(luaL_checkinteger(L, -1)));
        lua_pop(L, 1);
    }
    list<macro_arg_kind> arg_kinds = to_list(arg_kind_buffer.begin(), arg_kind_buffer.end());
    mtable.insert(mk_pair(macro_name, macro(arg_kinds, luaref(L, 3), prec)));
}

int mk_macro(lua_State * L) {
    mk_macro(L, get_expr_macros(L));
    return 0;
}

int mk_cmd_macro(lua_State * L) {
    mk_macro(L, get_cmd_macros(L));
    name macro_name = to_name_ext(L, 1);
    parser::imp * ptr = get_parser(L);
    if (!ptr)
        throw exception("invalid cmd_macro, it is not in the context of a Lean parser");
    // Make sure macro_name is a CommandId.
    ptr->m_scanner.add_command_keyword(macro_name);
    if (ptr->m_curr == scanner::token::Id && ptr->curr_name() == macro_name) {
        ptr->m_curr = scanner::token::CommandId;
    }
    return 0;
}

int mk_tactic_macro(lua_State * L) {
    mk_macro(L, get_tactic_macros(L));
    return 0;
}

static const struct luaL_Reg macros_m[] = {
    {"__gc",            macros_gc}, // never throws
    {0, 0}
};

void open_macros(lua_State * L) {
    luaL_newmetatable(L, macros_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, macros_m, 0);
    SET_GLOBAL_FUN(macros_pred, "is_macros");
    SET_GLOBAL_FUN(mk_macro, "macro");
    SET_GLOBAL_FUN(mk_cmd_macro, "cmd_macro");
    SET_GLOBAL_FUN(mk_tactic_macro, "tactic_macro");

    lua_newtable(L);
    SET_ENUM("Expr",     macro_arg_kind::Expr);
    SET_ENUM("Exprs",    macro_arg_kind::Exprs);
    SET_ENUM("Bindings", macro_arg_kind::Bindings);
    SET_ENUM("Id",       macro_arg_kind::Id);
    SET_ENUM("String",   macro_arg_kind::String);
    SET_ENUM("Int",      macro_arg_kind::Int);
    SET_ENUM("Comma",    macro_arg_kind::Comma);
    SET_ENUM("Assign",   macro_arg_kind::Assign);
    SET_ENUM("Tactic",   macro_arg_kind::Tactic);
    SET_ENUM("Tactics",  macro_arg_kind::Tactics);
    lua_setglobal(L, "macro_arg");
}
}

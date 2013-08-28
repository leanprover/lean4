/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include "scoped_map.h"
#include "exception.h"
#include "normalize.h"
#include "type_check.h"
#include "free_vars.h"
#include "builtin.h"
#include "arith.h"
#include "printer.h"
#include "state.h"
#include "option_declarations.h"
#include "expr_maps.h"
#include "sstream.h"
#include "kernel_exception.h"
#include "elaborator.h"
#include "lean_frontend.h"
#include "lean_parser.h"
#include "lean_scanner.h"
#include "lean_notation.h"
#include "lean_pp.h"
#ifdef LEAN_USE_READLINE
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <readline/readline.h>
#include <readline/history.h>
#endif

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
static name g_set_kwd("Set");
static name g_options_kwd("Options");
static name g_env_kwd("Environment");
static name g_import_kwd("Import");
static name g_help_kwd("Help");
/** \brief Table/List with all builtin command keywords */
static list<name> g_command_keywords = {g_definition_kwd, g_variable_kwd, g_theorem_kwd, g_axiom_kwd, g_universe_kwd, g_eval_kwd,
                                        g_show_kwd, g_check_kwd, g_infix_kwd, g_infixl_kwd, g_infixr_kwd, g_notation_kwd, g_echo_kwd,
                                        g_set_kwd, g_env_kwd, g_options_kwd, g_import_kwd, g_help_kwd};
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
static name g_unused(name(0u), "parser");

/**
    \brief Actual implementation for the parser functional object

    \remark It is an instance of a Pratt parser
    (http://en.wikipedia.org/wiki/Pratt_parser) described in the paper
    "Top down operator precedence". This algorithm is super simple,
    and it is easy to support user-defined infix/prefix/postfix/mixfix
    operators.
*/
class parser::imp {
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef std::unordered_map<name, expr, name_hash, name_eq>  builtins;
    typedef std::pair<unsigned, unsigned> pos_info;
    typedef expr_map<pos_info> expr_pos_info;
    frontend       m_frontend;
    scanner        m_scanner;
    elaborator     m_elaborator;
    scanner::token m_curr;
    bool           m_use_exceptions;
    bool           m_interactive;
    bool           m_found_errors;
    local_decls    m_local_decls;
    unsigned       m_num_local_decls;
    builtins       m_builtins;
    expr_pos_info  m_expr_pos_info;
    pos_info       m_last_cmd_pos;
    // Reference to temporary parser used to process import command.
    // We need this reference to be able to interrupt it.
    interruptable_ptr<parser>     m_import_parser;
    interruptable_ptr<normalizer> m_normalizer;

    bool           m_verbose;
    bool           m_show_errors;

    /** \brief Exception used to track parsing erros, it does not leak outside of this class. */
    struct parser_error : public exception {
        pos_info m_pos;
        parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
        parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
    };

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
    /** \brief Return true iff the current token is an integer */
    bool curr_is_int() const { return curr() == scanner::token::IntVal; }
    /** \brief Return true iff the current token is a '(' */
    bool curr_is_lparen() const { return curr() == scanner::token::LeftParen; }
    /** \brief Return true iff the current token is a '{' */
    bool curr_is_lcurly() const { return curr() == scanner::token::LeftCurlyBracket; }
    /** \brief Return true iff the current token is a ':' */
    bool curr_is_colon() const { return curr() == scanner::token::Colon; }
    /** \brief Return true iff the current token is a ',' */
    bool curr_is_comma() const { return curr() == scanner::token::Comma; }
    /** \brief Return true iff the current token is an 'in' token */
    bool curr_is_in() const { return curr() == scanner::token::In; }

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
    /** \brief Throws a parser error if the current token is not '('. If it is, move to the next token. */
    void check_lparen_next(char const * msg) { check_next(scanner::token::LeftParen, msg); }
    /** \brief Throws a parser error if the current token is not ')'. If it is, move to the next token. */
    void check_rparen_next(char const * msg) { check_next(scanner::token::RightParen, msg); }
    /** \brief Throws a parser error if the current token is not '}'. If it is, move to the next token. */
    void check_rcurly_next(char const * msg) { check_next(scanner::token::RightCurlyBracket, msg); }
    /** \brief Throws a parser error if the current token is not ':='. If it is, move to the next token. */
    void check_assign_next(char const * msg) { check_next(scanner::token::Assign, msg); }

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

    /** \brief Initialize \c m_builtins table with Lean builtin symbols that do not have notation associated with them. */
    void init_builtins() {
        m_builtins["Bool"]   = Bool;
        m_builtins["true"]   = True;
        m_builtins["false"]  = False;
        m_builtins["\u22A4"] = True;
        m_builtins["\u22A5"] = False;
        m_builtins["Int"]    = Int;
    }

    unsigned parse_unsigned(char const * msg) {
        lean_assert(curr_is_int());
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
        // TODO
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
        while (curr_is_identifier() || curr_is_int()) {
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
            return m_frontend.get_uvar(id);
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

    level parse_level_nud() {
        switch (curr()) {
        case scanner::token::Id:        return parse_level_nud_id();
        case scanner::token::IntVal:    return parse_level_nud_int();
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
       \brief Return the function associated with the given operator.
       If the operator has been overloaded, it returns an expression
       of the form (overload f_k ... (overload f_2 f_1) ...)
       where f_i's are different options.
       After we finish parsing, the procedure #elaborate will
       resolve/decide which f_i should be used.
    */
    expr mk_fun(operator_info const & op) {
        list<expr> const & fs = op.get_denotations();
        lean_assert(!is_nil(fs));
        auto it = fs.begin();
        expr r = *it;
        ++it;
        for (; it != fs.end(); ++it)
            r = mk_app(mk_overload_marker(), *it, r);
        return r;
    }

    /**
       \brief Create an application for the given operator and
       (explicit) arguments.
    */
    expr mk_application(operator_info const & op, pos_info const & pos, unsigned num_args, expr const * args) {
        buffer<expr> new_args;
        expr f = save(mk_fun(op), pos);
        new_args.push_back(f);
        // I'm using the fact that all denotations are compatible.
        // See lean_frontend.cpp for the definition of compatible denotations.
        expr const & d = head(op.get_denotations());
        if (is_constant(d) && m_frontend.has_implicit_arguments(const_name(d))) {
            std::vector<bool> const & imp_args = m_frontend.get_implicit_arguments(const_name(d));
            unsigned i = 0;
            for (unsigned j = 0; j < imp_args.size(); j++) {
                if (imp_args[j]) {
                    new_args.push_back(save(mk_metavar(), pos));
                } else {
                    if (i >= num_args)
                        throw parser_error(sstream() << "unexpected number of arguments for denotation with implicit arguments, it expects " << num_args << " explicit argument(s)", pos);
                    new_args.push_back(args[i]);
                    i++;
                }
            }
        } else {
            new_args.append(num_args, args);
        }
        return save(mk_app(new_args.size(), new_args.data()), pos);
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
        if(!curr_is_identifier() || curr_name() != op_part)
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
        object const & obj = m_frontend.find_object(id);
        if (obj) {
            object_kind k      = obj.kind();
            if (k == object_kind::Definition || k == object_kind::Postulate) {
                if (m_frontend.has_implicit_arguments(obj.get_name())) {
                    std::vector<bool> const & imp_args = m_frontend.get_implicit_arguments(obj.get_name());
                    buffer<expr> args;
                    args.push_back(save(mk_constant(obj.get_name()), pos()));
                    // We parse all the arguments to make sure we
                    // get all explicit arguments.
                    for (unsigned i = 0; i < imp_args.size(); i++) {
                        if (imp_args[i]) {
                            args.push_back(save(mk_metavar(), pos()));
                        } else {
                            args.push_back(parse_expr(1));
                        }
                    }
                    return mk_app(args.size(), args.data());
                } else {
                    return mk_constant(obj.get_name());
                }
            } else {
                throw parser_error(sstream() << "invalid object reference, object '" << id << "' is not an expression.", p);
            }
        }
        else {
            auto it = m_builtins.find(id);
            if (it != m_builtins.end()) {
                return it->second;
            } else {
                throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
            }
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
        } else {
            operator_info op = m_frontend.find_nud(id);
            if (op) {
                switch (op.get_fixity()) {
                case fixity::Prefix:  return parse_prefix(op);
                case fixity::Mixfixl: return parse_mixfixl(op);
                case fixity::Mixfixc: return parse_mixfixc(op);
                default: lean_unreachable(); return expr();
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
        } else {
            operator_info op = m_frontend.find_led(id);
            if (op) {
                switch (op.get_fixity()) {
                case fixity::Infix:   return parse_infix(left, op);
                case fixity::Infixl:  return parse_infixl(left, op);
                case fixity::Infixr:  return parse_infixr(left, op);
                case fixity::Mixfixr: return parse_mixfixr(left, op);
                case fixity::Mixfixo: return parse_mixfixo(left, op);
                case fixity::Postfix: return parse_postfix(left, op);
                default: lean_unreachable(); return expr();
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
        expr r = save(parse_expr(), p);
        check_rparen_next("invalid expression, ')' expected");
        return r;
    }

    /**
        \brief Parse a sequence of identifiers <tt>ID*</tt>. Store the
        result in \c result.
    */
    void parse_names(buffer<std::pair<pos_info, name>> & result) {
        while (curr_is_identifier()) {
            result.push_back(mk_pair(pos(), curr_name()));
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
    */
    void parse_simple_bindings(buffer<std::tuple<pos_info, name, expr, bool>> & result, bool implicit) {
        buffer<std::pair<pos_info, name>> names;
        parse_names(names);
        check_colon_next("invalid binder, ':' expected");
        unsigned sz = result.size();
        result.resize(sz + names.size());
        expr type = parse_expr();
        for (std::pair<pos_info, name> const & n : names) register_binding(n.second);
        unsigned i = names.size();
        while (i > 0) {
            --i;
            result[sz + i] = std::make_tuple(names[i].first, names[i].second, lift_free_vars(type, i), implicit);
        }
    }

    /**
        \brief Parse a sequence of <tt>'(' ID ... ID ':' expr ')'</tt>.

        This is used when parsing lambda, Pi, forall/exists expressions and definitions.
    */
    void parse_bindings(buffer<std::tuple<pos_info, name, expr, bool>> & result, bool allow_implicit = false) {
        if (curr_is_identifier()) {
            parse_simple_bindings(result, false);
        } else {
            // (ID ... ID : type) ... (ID ... ID : type)
            if (allow_implicit) {
                if (!curr_is_lparen() && !curr_is_lcurly())
                    throw parser_error("invalid binder, '(', '{' or identifier expected", pos());
            } else {
                if (!curr_is_lparen())
                    throw parser_error("invalid binder, '(' or identifier expected", pos());
            }
            bool implicit = curr_is_lcurly();
            next();
            parse_simple_bindings(result, implicit);
            if (!implicit)
                check_rparen_next("invalid binder, ')' expected");
            else
                check_rcurly_next("invalid binder, '}' expected");
            while (curr_is_lparen() || (allow_implicit && curr_is_lcurly())) {
                bool implicit = curr_is_lcurly();
                next();
                parse_simple_bindings(result, implicit);
                if (!implicit)
                    check_rparen_next("invalid binder, ')' expected");
                else
                    check_rcurly_next("invalid binder, '}' expected");
            }
        }
    }

    /**
        \brief Create a lambda/Pi abstraction, using the giving binders
        and body.
    */
    expr mk_abstraction(bool is_lambda, buffer<std::tuple<pos_info, name, expr, bool>> const & bindings, expr const & body) {
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
        buffer<std::tuple<pos_info, name, expr, bool>> bindings;
        parse_bindings(bindings);
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
        buffer<std::tuple<pos_info, name, expr, bool>> bindings;
        parse_bindings(bindings);
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
        buffer<std::tuple<pos_info, name, expr>> bindings;
        while (true) {
            auto p   = pos();
            name id  = check_identifier_next("invalid let expression, identifier expected");
            check_assign_next("invalid let expression, ':=' expected");
            expr val = parse_expr();
            register_binding(id);
            bindings.push_back(std::make_tuple(p, id, val));
            if (curr_is_in()) {
                next();
                expr r = parse_expr();
                unsigned i = bindings.size();
                while (i > 0) {
                    --i;
                    auto p = std::get<0>(bindings[i]);
                    r = save(mk_let(std::get<1>(bindings[i]), std::get<2>(bindings[i]), r), p);
                }
                return r;
            } else {
                check_comma_next("invalid let expression, ',' or 'in' expected");
            }
        }
    }

    /** \brief Parse an integer value. */
    expr parse_int() {
        auto p = pos();
        expr r = save(mk_int_value(m_scanner.get_num_val().get_numerator()), p);
        next();
        return r;
    }

    expr parse_decimal() {
        not_implemented_yet();
    }

    expr parse_string() {
        not_implemented_yet();
    }

    /** \brief Parse <tt>'Type'</tt> and <tt>'Type' level</tt> expressions. */
    expr parse_type() {
        auto p = pos();
        next();
        if (curr_is_identifier() || curr_is_int()) {
            return save(mk_type(parse_level()), p);
        } else {
            return Type();
        }
    }

    /** \brief Create a fresh metavariable. */
    expr mk_metavar() {
        return m_elaborator.mk_metavar(m_num_local_decls);
    }

    /** \brief Parse \c _ a hole that must be filled by the elaborator. */
    expr parse_placeholder() {
        auto p = pos();
        next();
        return save(mk_metavar(), p);
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
        case scanner::token::IntVal:      return parse_int();
        case scanner::token::DecimalVal:  return parse_decimal();
        case scanner::token::StringVal:   return parse_string();
        case scanner::token::Placeholder: return parse_placeholder();
        case scanner::token::Type:        return parse_type();
        default:
            throw parser_error("invalid expression, unexpected token", pos());
        }
    }

    /**
       \brief Auxiliary method used when processing the 'inside' of an expression.
    */
    expr parse_led(expr const & left) {
        switch (curr()) {
        case scanner::token::Id:          return parse_led_id(left);
        case scanner::token::Eq:          return parse_eq(left);
        case scanner::token::Arrow:       return parse_arrow(left);
        case scanner::token::LeftParen:   return mk_app(left, parse_lparen());
        case scanner::token::IntVal:      return mk_app(left, parse_int());
        case scanner::token::DecimalVal:  return mk_app(left, parse_decimal());
        case scanner::token::StringVal:   return mk_app(left, parse_string());
        case scanner::token::Placeholder: return mk_app(left, parse_placeholder());
        case scanner::token::Type:        return mk_app(left, parse_type());
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
                return 1;
            } else {
                operator_info op = m_frontend.find_led(id);
                if (op)
                    return op.get_precedence();
                else
                    return 1;
            }
        }
        case scanner::token::Eq : return g_eq_precedence;
        case scanner::token::Arrow : return g_arrow_precedence;
        case scanner::token::LeftParen: case scanner::token::IntVal: case scanner::token::DecimalVal:
        case scanner::token::StringVal: case scanner::token::Type: case scanner::token::Placeholder:
            return 1;
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

    expr elaborate(expr const & e) {
        if (has_metavar(e)) {
            // TODO fix
            regular(m_frontend) << e << endl;
            throw parser_error("expression contains metavariables... not implemented yet.", m_last_cmd_pos);
        } else {
            return e;
        }
    }

    /**
       @name Parse Commands
    */
    /*@{*/

    /**
        \brief Register implicit arguments for the definition or
        postulate named \c n. The fourth element in the tuple bindings
        is a flag indiciating whether the argument is implicit or not.
    */
    void register_implicit_arguments(name const & n, buffer<std::tuple<pos_info, name, expr,bool>> & bindings) {
        bool found = false;
        buffer<bool> imp_args;
        for (unsigned i = 0; i < bindings.size(); i++) {
            imp_args.push_back(std::get<3>(bindings[i]));
            if (imp_args.back())
                found = true;
        }
        if (found)
            m_frontend.mark_implicit_arguments(n, imp_args.size(), imp_args.data());
    }

    /** \brief Auxiliary method used for parsing definitions and theorems. */
    void parse_def_core(bool is_definition) {
        next();
        expr type, val;
        name id = check_identifier_next("invalid definition, identifier expected");
        buffer<std::tuple<pos_info, name, expr,bool>> bindings;
        if (curr_is_colon()) {
            next();
            type = elaborate(parse_expr());
            check_assign_next("invalid definition, ':=' expected");
            val  = elaborate(parse_expr());
        } else {
            mk_scope scope(*this);
            parse_bindings(bindings, true);
            check_colon_next("invalid definition, ':' expected");
            expr type_body = parse_expr();
            check_assign_next("invalid definition, ':=' expected");
            expr val_body  = parse_expr();
            type = elaborate(mk_abstraction(false, bindings, type_body));
            val  = elaborate(mk_abstraction(true, bindings, val_body));
        }
        if (is_definition) {
            m_frontend.add_definition(id, type, val);
            if (m_verbose)
                regular(m_frontend) << "  Defined: " << id << endl;
        } else {
            m_frontend.add_theorem(id, type, val);
            if (m_verbose)
                regular(m_frontend) << "  Proved: " << id << endl;
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
        buffer<std::tuple<pos_info, name, expr,bool>> bindings;
        expr type;
        if (curr_is_colon()) {
            next();
            type = elaborate(parse_expr());
        } else {
            mk_scope scope(*this);
            parse_bindings(bindings, true);
            check_colon_next("invalid variable/axiom declaration, ':' expected");
            expr type_body = parse_expr();
            type = elaborate(mk_abstraction(false, bindings, type_body));
        }
        if (is_var)
            m_frontend.add_var(id, type);
        else
            m_frontend.add_axiom(id, type);
        if (m_verbose)
            regular(m_frontend) << "  Assumed: " << id << endl;
        register_implicit_arguments(id, bindings);
    }

    /** \brief Parse one of the two forms:

        1) 'Variable' ID ':' type

        2) 'Variable' ID bindings ':' type
    */
    void parse_variable() {
        parse_variable_core(true);
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
        expr v = elaborate(parse_expr());
        normalizer norm(m_frontend);
        scoped_set_interruptable_ptr<normalizer> set(m_normalizer, &norm);
        expr r = norm(v);
        regular(m_frontend) << r << endl;
    }

    /** \brief Parse
           'Show' expr
           'Show' Environment [num]
           'Show' Options
    */
    void parse_show() {
        next();
        if (curr() == scanner::token::CommandId) {
            name opt_id = curr_name();
            next();
            if (opt_id == g_env_kwd) {
                if (curr_is_int()) {
                    unsigned i = parse_unsigned("invalid argument, value does not fit in a machine integer");
                    auto end = m_frontend.end_objects();
                    auto beg = m_frontend.begin_objects();
                    auto it  = end;
                    while (it != beg && i != 0) {
                        --i;
                        --it;
                    }
                    for (; it != end; ++it) {
                        regular(m_frontend) << *it << endl;
                    }
                } else {
                    regular(m_frontend) << m_frontend << endl;
                }
            } else if (opt_id == g_options_kwd) {
                regular(m_frontend) << m_frontend.get_state().get_options() << endl;
            } else {
                throw parser_error("invalid Show command, expression, 'Options' or 'Environment' expected", m_last_cmd_pos);
            }
        } else {
            expr v = elaborate(parse_expr());
            regular(m_frontend) << v << endl;
        }
    }

    /** \brief Parse 'Check' expr */
    void parse_check() {
        next();
        expr v = elaborate(parse_expr());
        expr t = infer_type(v, m_frontend);
        regular(m_frontend) << t << endl;
    }

    /** \brief Return the (optional) precedence of a user-defined operator. */
    unsigned parse_precedence() {
        if (curr_is_int()) {
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
        case fixity::Infix:   m_frontend.add_infix(op_id, prec, d); break;
        case fixity::Infixl:  m_frontend.add_infixl(op_id, prec, d); break;
        case fixity::Infixr:  m_frontend.add_infixr(op_id, prec, d); break;
        default: lean_unreachable(); break;
        }
    }

    /**
       \brief Parse notation declaration unified format

       'Notation' [Num] parts ':' ID
    */
    void parse_notation_decl() {
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
                        throw parser_error("invalid notation declaration, it must have at least one identifier", pos());
                    }
                    name name_id = check_identifier_next("invalid notation declaration, identifier expected");
                    expr d     = mk_constant(name_id);
                    if (parts.size() == 1) {
                        if (first_placeholder && prev_placeholder) {
                            // infix: _ ID _
                            m_frontend.add_infix(parts[0], prec, d);
                        } else if (first_placeholder) {
                            // postfix: _ ID
                            m_frontend.add_postfix(parts[0], prec, d);
                        } else if (prev_placeholder) {
                            // prefix: ID _
                            m_frontend.add_prefix(parts[0], prec, d);
                        } else {
                            lean_unreachable();
                        }
                    } else {
                        if (first_placeholder && prev_placeholder) {
                            // mixfixo: _ ID ... ID _
                            m_frontend.add_mixfixo(parts.size(), parts.data(), prec, d);
                        } else if (first_placeholder) {
                            // mixfixr: _ ID ... ID
                            m_frontend.add_mixfixr(parts.size(), parts.data(), prec, d);
                        } else if (prev_placeholder) {
                            // mixfixl: ID _ ... ID _
                            m_frontend.add_mixfixl(parts.size(), parts.data(), prec, d);
                        } else {
                            // mixfixc: ID _ ... _ ID
                            m_frontend.add_mixfixc(parts.size(), parts.data(), prec, d);
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
        regular(m_frontend) << msg << endl;
    }

    /** Parse 'Set' [id] [value] */
    void parse_set() {
        next();
        auto id_pos = pos();
        name id = check_identifier_next("invalid set options, identifier (i.e., option name) expected");
        auto decl_it = get_option_declarations().find(id);
        if (decl_it == get_option_declarations().end())
            throw parser_error(sstream() << "unknown option '" << id << "', type 'Help Options.' for list of available options", id_pos);
        option_kind k = decl_it->second.kind();
        switch (curr()) {
        case scanner::token::Id:
            if (k != BoolOption)
                throw parser_error(sstream() << "invalid option value, given option is not Boolean", pos());
            if (curr_name() == "true")
                m_frontend.set_option(id, true);
            else if (curr_name() == "false")
                m_frontend.set_option(id, false);
            else
                throw parser_error("invalid Boolean option value, 'true' or 'false' expected", pos());
            break;
        case scanner::token::StringVal:
            if (k != StringOption)
                throw parser_error("invalid option value, given option is not a string", pos());
            m_frontend.set_option(id, curr_string());
            break;
        case scanner::token::IntVal:
            if (k != IntOption && k != UnsignedOption)
                throw parser_error("invalid option value, given option is not an integer", pos());
            m_frontend.set_option(id, parse_unsigned("invalid option value, value does not fit in a machine integer"));
            break;
        case scanner::token::DecimalVal:
            if (k != DoubleOption)
                throw parser_error("invalid option value, given option is not floating point value", pos());
            m_frontend.set_option(id, parse_double());
            break;
        default:
            throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", pos());
        }
        updt_options();
        if (m_verbose)
            regular(m_frontend) << "  Set option: " << id << endl;
        next();
    }

    void parse_import() {
        next();
        std::string fname = check_string_next("invalid import command, string (i.e., file name) expected");
        std::ifstream in(fname);
        if (!in.is_open())
            throw parser_error(sstream() << "invalid import command, failed to open file '" << fname << "'", m_last_cmd_pos);
        try {
            if (m_verbose)
                regular(m_frontend) << "Importing file '" << fname << "'" << endl;
            parser import_parser(m_frontend, in, true /* use exceptions */, false /* not interactive */);
            scoped_set_interruptable_ptr<parser> set(m_import_parser, &import_parser);
            import_parser();
        } catch (interrupted &) {
            throw;
        } catch (exception &) {
            throw parser_error(sstream() << "failed to import file '" << fname << "'", m_last_cmd_pos);
        }
    }

    void parse_help() {
        next();
        if (curr() == scanner::token::CommandId) {
            name opt_id = curr_name();
            next();
            if (opt_id == g_options_kwd) {
                regular(m_frontend) << "Available options:" << endl;
                for (auto p : get_option_declarations()) {
                    auto opt = p.second;
                    regular(m_frontend) << "  " << opt.get_name() << " (" << opt.kind() << ") " << opt.get_description() << " (default: " << opt.get_default_value() << ")" << endl;
                }
            } else {
                throw parser_error("invalid help command", m_last_cmd_pos);
            }
        } else {
            regular(m_frontend) << "Available commands:" << endl
                                << "  Axiom [id] : [type]    assert/postulate a new axiom" << endl
                                << "  Check [expr]           type check the given expression" << endl
                                << "  Definition [id] : [type] := [expr]   define a new element" << endl
                                << "  Theorem [id] : [type] := [expr]      define a new theorem" << endl
                                << "  Echo [string]          display the given string" << endl
                                << "  Eval [expr]            evaluate the given expression" << endl
                                << "  Help                   display this message" << endl
                                << "  Help Options           display available options" << endl
                                << "  Help Notation          describe commands for defining infix,mixfix,postfix operators" << endl
                                << "  Import [string]        load the given file" << endl
                                << "  Set [id] [value]       set option [id] with value [value]" << endl
                                << "  Show [expr]            pretty print the given expression" << endl
                                << "  Show Options           show current the set of assigned options" << endl
                                << "  Show Environment       show objects in the environment, if [Num] provided, then show only the last [Num] objects" << endl
                                << "  Show Environment [num] show the last num objects in the environment" << endl
                                << "  Variable [id] : [type] declare/postulate an element of the given type" << endl
                                << "  Universe [id] [level]  declare a new universe variable that is >= the given level" << endl
                                << "Type Ctrl-D to exit" << endl;
        }
    }

    /** \brief Parse a Lean command. */
    void parse_command() {
        m_elaborator.clear();
        m_expr_pos_info.clear();
        m_last_cmd_pos = pos();
        name const & cmd_id = curr_name();
        if (cmd_id == g_definition_kwd)    parse_definition();
        else if (cmd_id == g_variable_kwd) parse_variable();
        else if (cmd_id == g_theorem_kwd)  parse_theorem();
        else if (cmd_id == g_axiom_kwd)    parse_axiom();
        else if (cmd_id == g_eval_kwd)     parse_eval();
        else if (cmd_id == g_show_kwd)     parse_show();
        else if (cmd_id == g_check_kwd)    parse_check();
        else if (cmd_id == g_infix_kwd)    parse_op(fixity::Infix);
        else if (cmd_id == g_infixl_kwd)   parse_op(fixity::Infixl);
        else if (cmd_id == g_infixr_kwd)   parse_op(fixity::Infixr);
        else if (cmd_id == g_notation_kwd) parse_notation_decl();
        else if (cmd_id == g_echo_kwd)     parse_echo();
        else if (cmd_id == g_set_kwd)      parse_set();
        else if (cmd_id == g_import_kwd)   parse_import();
        else if (cmd_id == g_help_kwd)     parse_help();
        else { next(); throw parser_error(sstream() << "invalid command '" << cmd_id << "'", m_last_cmd_pos); }
    }
    /*@}*/

    void display_error_pos(unsigned line, unsigned pos) { regular(m_frontend) << "Error (line: " << line << ", pos: " << pos << ")"; }
    void display_error_pos(pos_info const & p) { display_error_pos(p.first, p.second); }
    void display_error_pos(expr const & e) {
        if (e) {
            auto it = m_expr_pos_info.find(e);
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
        regular(m_frontend) << " " << msg << endl;
        sync();
    }
    void display_error(char const * msg) {
        display_error(msg, m_scanner.get_line(), m_scanner.get_pos());
    }
    void display_error(kernel_exception const & ex) {
        display_error_pos(ex.get_main_expr());
        regular(m_frontend) << " " << ex << endl;
        sync();
    }

    void updt_options() {
        m_verbose = get_parser_verbose(m_frontend.get_state().get_options());
        m_show_errors = get_parser_show_errors(m_frontend.get_state().get_options());
    }

    /** \brief Keep consuming tokens until we find a Command or End-of-file. */
    void sync() {
        show_prompt();
        while (curr() != scanner::token::CommandId && curr() != scanner::token::Eof)
            next();
    }

public:
    imp(frontend & fe, std::istream & in, bool use_exceptions, bool interactive):
        m_frontend(fe),
        m_scanner(in),
        m_elaborator(fe),
        m_use_exceptions(use_exceptions),
        m_interactive(interactive) {
        updt_options();
        m_found_errors = false;
        m_num_local_decls = 0;
        m_scanner.set_command_keywords(g_command_keywords);
        init_builtins();
        scan();
    }

    static void show_prompt(bool interactive, frontend const & fe) {
        if (interactive) {
            regular(fe) << "# ";
            regular(fe).flush();
        }
    }

    void show_prompt() {
        show_prompt(m_interactive, m_frontend);
    }

    /** \brief Parse a sequence of commands. This method also perform error management. */
    bool parse_commands() {
        while (true) {
            try {
                switch (curr()) {
                case scanner::token::CommandId: parse_command(); break;
                case scanner::token::Period: show_prompt(); next(); break;
                case scanner::token::Eof: return !m_found_errors;
                default:
                    throw parser_error("Command expected", pos());
                }
            } catch (parser_error & ex) {
                m_found_errors = true;
                if (m_show_errors)
                    display_error(ex.what(), ex.m_pos.first, ex.m_pos.second);
                if (m_use_exceptions) {
                    throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
                }
            } catch (kernel_exception & ex) {
                m_found_errors = true;
                if (m_show_errors)
                    display_error(ex);
                if (m_use_exceptions)
                    throw;
            } catch (interrupted & ex) {
                if (m_verbose)
                    regular(m_frontend) << "\n!!!Interrupted!!!" << endl;
                reset_interrupt();
                sync();
                if (m_use_exceptions)
                    throw;
            } catch (exception & ex) {
                m_found_errors = true;
                if (m_show_errors)
                    display_error(ex.what());
                if (m_use_exceptions)
                    throw;
            }
        }
    }

    /** \brief Parse an expression. */
    expr parse_expr_main() {
        try {
            return elaborate(parse_expr());
        } catch (parser_error & ex) {
            throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
        }
    }

    void set_interrupt(bool flag) {
        m_frontend.set_interrupt(flag);
        m_elaborator.set_interrupt(flag);
        m_import_parser.set_interrupt(flag);
        m_normalizer.set_interrupt(flag);
    }

    void reset_interrupt() {
        set_interrupt(false);
    }
};

parser::parser(frontend fe, std::istream & in, bool use_exceptions, bool interactive) {
    parser::imp::show_prompt(interactive, fe);
    m_ptr.reset(new imp(fe, in, use_exceptions, interactive));
}

parser::~parser() {
}

bool parser::operator()() {
    return m_ptr->parse_commands();
}

void parser::set_interrupt(bool flag) {
    m_ptr->set_interrupt(flag);
}

expr parser::parse_expr() {
    return m_ptr->parse_expr_main();
}

shell::shell(frontend & fe):m_frontend(fe) {
}

shell::~shell() {
}

bool shell::operator()() {
#ifdef LEAN_USE_READLINE
    bool errors = false;
    char * input;
    while (true) {
        input = readline("# ");
        if (!input)
            return errors;
        add_history(input);
        std::istringstream strm(input);
        {
            parser p(m_frontend, strm, false, false);
            scoped_set_interruptable_ptr<parser> set(m_parser, &p);
            if (!p())
                errors = true;
        }
        free(input);
    }
#else
    parser p(m_frontend, std::cin, false, true);
    scoped_set_interruptable_ptr<parser> set(m_parser, &p);
    return p();
#endif
}

void shell::set_interrupt(bool flag) {
    m_parser.set_interrupt(flag);
}
}

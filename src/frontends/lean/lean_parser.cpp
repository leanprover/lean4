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

namespace lean {
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
static name g_prefix_kwd("Prefix");
static name g_postfix_kwd("Postfix");
static name g_mixfixl_kwd("Mixfixl");
static name g_mixfixr_kwd("Mixfixr");
static name g_mixfixc_kwd("Mixfixc");
static name g_echo_kwd("Echo");
static name g_set_kwd("Set");
static name g_options_kwd("Options");
static name g_env_kwd("Environment");
static name g_import_kwd("Import");
static name g_help_kwd("Help");
/** \brief Table/List with all builtin command keywords */
static list<name> g_command_keywords = {g_definition_kwd, g_variable_kwd, g_theorem_kwd, g_axiom_kwd, g_universe_kwd, g_eval_kwd,
                                        g_show_kwd, g_check_kwd, g_infix_kwd, g_infixl_kwd, g_infixr_kwd, g_prefix_kwd,
                                        g_postfix_kwd, g_mixfixl_kwd, g_mixfixr_kwd, g_mixfixc_kwd, g_echo_kwd,
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

// ==========================================
// Auxiliary constant used to mark applications of overloaded operators.
static name g_overload_name(name(name(name(0u), "parser"), "overload"));
static expr g_overload = mk_constant(g_overload_name);
// ==========================================

// A name that can't be created by the user.
// It is used as placeholder for parsing A -> B expressions which
// are syntax sugar for (Pi (_ : A), B)
static name g_unused(name(0u), "parser");

/**
    \brief Functional object for parsing

    \remark It is an instance of a Pratt parser
    (http://en.wikipedia.org/wiki/Pratt_parser) described in the paper
    "Top down operator precedence". This algorithm is super simple,
    and it is easy to support user-defined infix/prefix/postfix/mixfix
    operators.
*/
class parser_fn {
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef std::unordered_map<name, expr, name_hash, name_eq>  builtins;
    typedef std::pair<unsigned, unsigned> pos_info;
    typedef expr_map<pos_info> expr_pos_info;
    frontend       m_frontend;
    scanner        m_scanner;
    scanner::token m_curr;
    bool           m_use_exceptions;
    bool           m_interactive;
    bool           m_found_errors;
    local_decls    m_local_decls;
    unsigned       m_num_local_decls;
    builtins       m_builtins;
    expr_pos_info  m_expr_pos_info;
    pos_info       m_last_cmd_pos;

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
        parser_fn &           m_fn;
        local_decls::mk_scope m_scope;
        unsigned              m_old_num_local_decls;
        mk_scope(parser_fn & fn):m_fn(fn), m_scope(fn.m_local_decls), m_old_num_local_decls(fn.m_num_local_decls) {}
        ~mk_scope() { m_fn.m_num_local_decls = m_old_num_local_decls; }
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
    /** \brief Keep consume tokens until we find a Command or End-of-file. */
    void sync() {
        while (curr() != scanner::token::CommandId && curr() != scanner::token::Eof)
            next();
    }

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

    /** \brief Return true iff the current toke is an identifier */
    bool curr_is_identifier() const { return curr() == scanner::token::Id; }
    /** \brief Return true iff the current toke is an integer */
    bool curr_is_int() const { return curr() == scanner::token::IntVal; }
    /** \brief Return true iff the current toke is a '(' */
    bool curr_is_lparen() const { return curr() == scanner::token::LeftParen; }
    /** \brief Return true iff the current toke is a ':' */
    bool curr_is_colon() const { return curr() == scanner::token::Colon; }
    /** \brief Return true iff the current toke is a ',' */
    bool curr_is_comma() const { return curr() == scanner::token::Comma; }
    /** \brief Return true iff the current toke is an 'in' token */
    bool curr_is_in() const { return curr() == scanner::token::In; }

    /** \brief Throws a parser error if the current token is not an identifier. */
    void check_identifier(char const * msg) { if (!curr_is_identifier()) throw parser_error(msg, pos()); }
    /**
        \brief Throws a parser error if the current token is not an
        identifier. If it is, move to the next token.
    */
    name check_identifier_next(char const * msg) { check_identifier(msg); name r = curr_name(); next(); return r; }
    /** \brief Throws a parser error if the current token is not ':'. If it is, move to the next token. */
    void check_colon_next(char const * msg) { check_next(scanner::token::Colon, msg); }
    /** \brief Throws a parser error if the current token is not ','. If it is, move to the next token. */
    void check_comma_next(char const * msg) { check_next(scanner::token::Comma, msg); }
    /** \brief Throws a parser error if the current token is not '('. If it is, move to the next token. */
    void check_lparen_next(char const * msg) { check_next(scanner::token::LeftParen, msg); }
    /** \brief Throws a parser error if the current token is not ')'. If it is, move to the next token. */
    void check_rparen_next(char const * msg) { check_next(scanner::token::RightParen, msg); }
    /** \brief Throws a parser error if the current token is not ':='. If it is, move to the next token. */
    void check_assign_next(char const * msg) { check_next(scanner::token::Assign, msg); }
    /** \brief Throws a parser error if the current token is not an identifier named \c op. */
    void check_name(name const & op, char const * msg) { if(!curr_is_identifier() || curr_name() != op) throw parser_error(msg, pos()); }
    /** \brief Throws a parser error if the current token is not an identifier named \c op. If it is, move to the next token. */
    void check_name_next(name const & op, char const * msg) { check_name(op, msg); next(); }
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
        list<expr> const & fs = op.get_exprs();
        lean_assert(!is_nil(fs));
        auto it = fs.begin();
        expr r = *it;
        ++it;
        for (; it != fs.end(); ++it)
            r = mk_app(g_overload, *it, r);
        return r;
    }

    /** \brief Parse a user defined prefix operator. */
    expr parse_prefix(operator_info const & op) {
        auto p = pos();
        expr f = save(mk_fun(op), p);
        expr arg = parse_expr(op.get_precedence());
        return save(mk_app(f, arg), p);
    }

    /** \brief Parse a user defined postfix operator. */
    expr parse_postfix(expr const & left, operator_info const & op) {
        auto p = pos();
        expr f = save(mk_fun(op), p);
        return save(mk_app(f, left), p);
    }

    /** \brief Parse a user defined infix operator. */
    expr parse_infix(expr const & left, operator_info const & op) {
        auto p = pos();
        expr f = save(mk_fun(op), p);
        expr right = parse_expr(op.get_precedence()+1);
        return save(mk_app(f, left, right), p);
    }

    /** \brief Parse a user defined infix-left operator. */
    expr parse_infixl(expr const & left, operator_info const & op) {
        auto p = pos();
        expr f = save(mk_fun(op), p);
        expr right = parse_expr(op.get_precedence());
        return save(mk_app(f, left, right), p);
    }

    /** \brief Parse a user defined infix-right operator. */
    expr parse_infixr(expr const & left, operator_info const & op) {
        auto p = pos();
        expr f = save(mk_fun(op), p);
        expr right = parse_expr(op.get_precedence()-1);
        return save(mk_app(f, left, right), p);
    }

    /**
        \brief Throws an error if the current token is not an identifier named \c op_part.
        If it is, move to the next toke. The error message assumes
        this method has been used when parsing mixfix operators.
    */
    void check_op_part(name const & op_part) {
        check_name_next(op_part, "invalid mixfix operator application, identifier expected");
    }

    /** \brief Auxiliary function for #parse_mixfixl and #parse_mixfixr */
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
        expr f = save(mk_fun(op), p);
        buffer<expr> args;
        args.push_back(f);
        args.push_back(parse_expr(op.get_precedence()));
        parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
        return save(mk_app(args.size(), args.data()), p);
    }

    /** \brief Parse user defined mixfixr operator. It has the form: _ ID ... _ ID */
    expr parse_mixfixr(expr const & left, operator_info const & op) {
        auto p = pos();
        expr f = save(mk_fun(op), p);
        buffer<expr> args;
        args.push_back(f);
        args.push_back(left);
        parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
        return save(mk_app(args.size(), args.data()), p);
    }

    /** \brief Parse user defined mixfixc operator. It has the form: ID _ ID ... _ ID */
    expr parse_mixfixc(operator_info const & op) {
        auto p = pos();
        expr f = save(mk_fun(op), p);
        buffer<expr> args;
        args.push_back(f);
        args.push_back(parse_expr(op.get_precedence()));
        list<name> const & ops = op.get_op_name_parts();
        auto it = ops.begin();
        ++it;
        while (true) {
            check_op_part(*it);
            ++it;
            if (it == ops.end())
                return save(mk_app(args.size(), args.data()), p);
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
            if (k == object_kind::Definition || k == object_kind::Postulate)
                return mk_constant(obj.get_name());
            else
                throw parser_error(sstream() << "invalid object reference, object '" << id << "' is not an expression.", p);
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
    void parse_simple_bindings(buffer<std::tuple<pos_info, name, expr>> & result) {
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
            result[sz + i] = std::make_tuple(names[i].first, names[i].second, lift_free_vars(type, i));
        }
    }

    /**
        \brief Parse a sequence of <tt>'(' ID ... ID ':' expr ')'</tt>.

        This is used when parsing lambda, Pi, forall/exists expressions and definitions.
    */
    void parse_bindings(buffer<std::tuple<pos_info, name, expr>> & result) {
        if (curr_is_identifier()) {
            parse_simple_bindings(result);
        } else {
            // (ID ... ID : type) ... (ID ... ID : type)
            check_lparen_next("invalid binder, '(' or identifier expected");
            parse_simple_bindings(result);
            check_rparen_next("invalid binder, ')' expected");
            while (curr_is_lparen()) {
                next();
                parse_simple_bindings(result);
                check_rparen_next("invalid binder, ')' expected");
            }
        }
    }

    /**
        \brief Create a lambda/Pi abstraction, using the giving binders
        and body.
    */
    expr mk_abstraction(bool is_lambda, buffer<std::tuple<pos_info, name, expr>> const & bindings, expr const & body) {
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
        buffer<std::tuple<pos_info, name, expr>> bindings;
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
        buffer<std::tuple<pos_info, name, expr>> bindings;
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

    /**
       \brief Auxiliary method used when processing the beginning of an expression.
    */
    expr parse_nud() {
        switch (curr()) {
        case scanner::token::Id:         return parse_nud_id();
        case scanner::token::LeftParen:  return parse_lparen();
        case scanner::token::Lambda:     return parse_lambda();
        case scanner::token::Pi:         return parse_pi();
        case scanner::token::Forall:     return parse_forall();
        case scanner::token::Exists:     return parse_exists();
        case scanner::token::Let:        return parse_let();
        case scanner::token::IntVal:     return parse_int();
        case scanner::token::DecimalVal: return parse_decimal();
        case scanner::token::StringVal:  return parse_string();
        case scanner::token::Type:       return parse_type();
        default:
            throw parser_error("invalid expression, unexpected token", pos());
        }
    }

    /**
       \brief Auxiliary method used when processing the 'inside' of an expression.
    */
    expr parse_led(expr const & left) {
        switch (curr()) {
        case scanner::token::Id:         return parse_led_id(left);
        case scanner::token::Eq:         return parse_eq(left);
        case scanner::token::Arrow:      return parse_arrow(left);
        case scanner::token::LeftParen:  return mk_app(left, parse_lparen());
        case scanner::token::IntVal:     return mk_app(left, parse_int());
        case scanner::token::DecimalVal: return mk_app(left, parse_decimal());
        case scanner::token::StringVal:  return mk_app(left, parse_string());
        case scanner::token::Type:       return mk_app(left, parse_type());
        default:                         return left;
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
        case scanner::token::StringVal: case scanner::token::Type:
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
        // TODO
        return e;
    }

    /**
       @name Parse Commands
    */
    /*@{*/
    /** \brief Auxiliary method used for parsing definitions and theorems. */
    void parse_def_core(bool is_definition) {
        next();
        expr type, val;
        name id = check_identifier_next("invalid definition, identifier expected");
        if (curr_is_colon()) {
            next();
            type = elaborate(parse_expr());
            check_assign_next("invalid definition, ':=' expected");
            val  = elaborate(parse_expr());
        } else {
            mk_scope scope(*this);
            buffer<std::tuple<pos_info, name, expr>> bindings;
            parse_bindings(bindings);
            check_colon_next("invalid definition, ':' expected");
            expr type_body = parse_expr();
            check_assign_next("invalid definition, ':=' expected");
            expr val_body  = parse_expr();
            type = elaborate(mk_abstraction(false, bindings, type_body));
            val  = elaborate(mk_abstraction(true, bindings, val_body));
        }
        if (is_definition) {
            m_frontend.add_definition(id, type, val);
            regular(m_frontend) << "  Defined: " << id << endl;
        } else {
            m_frontend.add_theorem(id, type, val);
            regular(m_frontend) << "  Proved: " << id << endl;
        }
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

    /** \brief Parse 'Variable' ID ':' expr */
    void parse_variable() {
        next();
        name id = check_identifier_next("invalid variable declaration, identifier expected");
        check_colon_next("invalid variable declaration, ':' expected");
        expr type = elaborate(parse_expr());
        m_frontend.add_var(id, type);
        regular(m_frontend) << "  Assumed: " << id << endl;
    }

    /** \brief Parse 'Axiom' ID ':' expr */
    void parse_axiom() {
        next();
        name id = check_identifier_next("invalid axiom, identifier expected");
        check_colon_next("invalid axiom, ':' expected");
        expr type = elaborate(parse_expr());
        m_frontend.add_axiom(id, type);
        regular(m_frontend) << "  Assumed: " << id << endl;
    }

    /** \brief Parse 'Eval' expr */
    void parse_eval() {
        next();
        expr v = elaborate(parse_expr());
        expr r = normalize(v, m_frontend);
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

           - fixity [Num] ID ':' expr
    */
    void parse_op(fixity fx) {
        next();
        unsigned prec = parse_precedence();
        name op_id = parse_op_id();
        check_colon_next("invalid operator definition, ':' expected");
        expr d     = parse_expr();
        switch (fx) {
        case fixity::Prefix:  m_frontend.add_prefix(op_id, prec, d); break;
        case fixity::Postfix: m_frontend.add_postfix(op_id, prec, d); break;
        case fixity::Infix:   m_frontend.add_infix(op_id, prec, d); break;
        case fixity::Infixl:  m_frontend.add_infixl(op_id, prec, d); break;
        case fixity::Infixr:  m_frontend.add_infixr(op_id, prec, d); break;
        default: lean_unreachable(); break;
        }
    }

    /**
        \brief Parse mixfix/mixfixl/mixfixr user operator definition.
        These definitions have the form:

        - fixity [NUM] ID ID+ ':' ID
    */
    void parse_mixfix_op(fixity fx) {
        next();
        unsigned prec = parse_precedence();
        buffer<name> parts;
        parts.push_back(parse_op_id());
        parts.push_back(parse_op_id());
        while (!curr_is_colon()) {
            parts.push_back(parse_op_id());
        }
        lean_assert(curr_is_colon());
        next();
        expr d = parse_expr();
        switch (fx) {
        case fixity::Mixfixl:  m_frontend.add_mixfixl(parts.size(), parts.data(), prec, d); break;
        case fixity::Mixfixr:  m_frontend.add_mixfixr(parts.size(), parts.data(), prec, d); break;
        case fixity::Mixfixc:  m_frontend.add_mixfixc(parts.size(), parts.data(), prec, d); break;
        default: lean_unreachable(); break;
        }
    }

    void parse_echo() {
        next();
        std::string msg = check_string_next("invalid echo command, string expected");
        regular(m_frontend) << msg << endl;
    }

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
        regular(m_frontend) << "  Set option: " << id << endl;
        next();
    }

    void parse_import() {
        next();
        std::string fname = check_string_next("invalid import command, string (i.e., file name) expected");
        std::ifstream in(fname);
        if (!in.is_open())
            throw parser_error(sstream() << "invalid import command, failed to open file '" << fname << "'", m_last_cmd_pos);
        ::lean::parse_commands(m_frontend, in, m_use_exceptions, false);
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
        m_frontend.reset_interrupt();
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
        else if (cmd_id == g_prefix_kwd)   parse_op(fixity::Prefix);
        else if (cmd_id == g_postfix_kwd)  parse_op(fixity::Postfix);
        else if (cmd_id == g_mixfixl_kwd)  parse_mixfix_op(fixity::Mixfixl);
        else if (cmd_id == g_mixfixr_kwd)  parse_mixfix_op(fixity::Mixfixr);
        else if (cmd_id == g_mixfixc_kwd)  parse_mixfix_op(fixity::Mixfixc);
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

public:
    parser_fn(frontend & fe, std::istream & in, bool use_exceptions, bool interactive):
        m_frontend(fe),
        m_scanner(in),
        m_use_exceptions(use_exceptions),
        m_interactive(interactive) {
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
                if (m_use_exceptions) {
                    throw parser_exception(ex.what(), ex.m_pos.first, ex.m_pos.second);
                } else {
                    display_error(ex.what(), ex.m_pos.first, ex.m_pos.second);
                }
            } catch (kernel_exception & ex) {
                m_found_errors = true;
                if (m_use_exceptions) {
                    throw;
                } else {
                    display_error(ex);
                }
            } catch (interrupted & ex) {
                if (m_use_exceptions) {
                    throw;
                } else {
                    regular(m_frontend) << "\n!!!Interrupted!!!" << endl;
                    sync();
                }
            } catch (exception & ex) {
                m_found_errors = true;
                if (m_use_exceptions) {
                    throw;
                } else {
                    display_error(ex.what());
                }
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
};
bool parse_commands(frontend & fe, std::istream & in, bool use_exceptions, bool interactive) {
    parser_fn::show_prompt(interactive, fe);
    return parser_fn(fe, in, use_exceptions, interactive).parse_commands();
}
bool parse_commands_from_stdin(frontend & fe) {
#ifdef LEAN_USE_READLINE
    bool errors = false;
    char * input;
    while (true) {
        input = readline("# ");
        if (!input)
            return errors;
        add_history(input);
        std::istringstream strm(input);
        if (!parse_commands(fe, strm, false, false))
            errors = true;
        free(input);
    }
#else
    return parse_commands(fe, std::cin, false, true) ? 0 : 1;
#endif
}
expr parse_expr(frontend const & fe, std::istream & in) {
    return parser_fn(const_cast<frontend&>(fe), in, true, false).parse_expr_main();
}
}

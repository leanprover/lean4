/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include "frontend.h"
#include "scanner.h"
#include "scoped_map.h"
#include "exception.h"
#include "builtin.h"
#include "arith.h"

namespace lean {
static name g_definition_kwd("Definition");
static name g_variable_kwd("Variable");
static name g_theorem_kwd("Theorem");
static name g_axiom_kwd("Axiom");
static name g_universe_kwd("Universe");
static name g_eval_kwd("Eval");
static name g_show_kwd("Show");
static name g_infix_kwd("Infix");
static name g_infixl_kwd("Infixl");
static name g_infixr_kwd("Infixr");
static name g_prefix_kwd("Prefix");
static name g_postfix_kwd("Postfix");
static name g_mixfixl_kwd("Mixfixl");
static name g_mixfixr_kwd("Mixfixr");
static name g_mixfixc_kwd("Mixfixc");

static name g_overload_name(name(name(name(0u), "parser"), "overload"));
static expr g_overload = mk_constant(g_overload_name);

static list<name> g_command_keywords = {g_definition_kwd, g_variable_kwd, g_theorem_kwd, g_axiom_kwd, g_universe_kwd, g_eval_kwd, g_show_kwd, g_infix_kwd, g_infixl_kwd, g_infixr_kwd, g_prefix_kwd, g_postfix_kwd, g_mixfixl_kwd, g_mixfixr_kwd, g_mixfixc_kwd};

/** \brief Functional object for parsing */
struct parser_fn {
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef std::unordered_map<name, expr, name_hash, name_eq>  builtins;
    frontend       m_frontend;
    scanner        m_scanner;
    std::ostream & m_err;
    scanner::token m_curr;
    bool           m_use_exceptions;
    bool           m_found_errors;
    local_decls    m_local_decls;
    builtins       m_builtins;

    /** \brief Exception used to track parsing erros, it does not leak outside of this class. */
    struct parser_error : public exception {
        parser_error(char const * msg):exception(msg) {}
    };

    void scan() { m_curr = m_scanner.scan(); }
    scanner::token curr() const { return m_curr; }
    void next() { if (m_curr != scanner::token::Eof) scan(); }
    void sync() {
        while (curr() != scanner::token::CommandId && curr() != scanner::token::Eof)
            next();
    }
    name const & curr_name() const { return m_scanner.get_name_val(); }

    void check_next(scanner::token t, char const * msg) {
        if (curr() == t)
            next();
        else
            throw parser_error(msg);
    }

    bool curr_is_identifier() const { return curr() == scanner::token::Id; }

    void check_identifier(char const * msg) { if (!curr_is_identifier()) throw parser_error(msg); }
    name check_identifier_next(char const * msg) { check_identifier(msg); name r = curr_name(); next(); return r; }
    void check_colon_next(char const * msg) { check_next(scanner::token::Colon, msg); }
    void check_rparen_next(char const * msg) { check_next(scanner::token::RightParen, msg); }

    void init_builtins() {
        m_builtins["Bool"]   = Bool;
        m_builtins["true"]   = True;
        m_builtins["false"]  = False;
        m_builtins["\u22A4"] = True;
        m_builtins["\u22A5"] = False;
        m_builtins["Int"]    = Int;
    }

    parser_fn(frontend & fe, std::istream & in, std::ostream & err, bool use_exceptions):
        m_frontend(fe),
        m_scanner(in),
        m_err(err),
        m_use_exceptions(use_exceptions) {
        m_found_errors = false;
        m_scanner.set_command_keywords(g_command_keywords);
        init_builtins();
        scan();
    }

    [[ noreturn ]] void not_implemented_yet() {
        throw parser_error("not implemented yet");
    }

    expr mk_fun(operator_info const & op) {
        list<name> const & fs = op.get_internal_names();
        lean_assert(!is_nil(fs));
        auto it = fs.begin();
        expr r = mk_constant(*it);
        ++it;
        for (; it != fs.end(); ++it)
            r = mk_app(g_overload, r, mk_constant(*it));
        return r;
    }

    expr parse_prefix(operator_info const & op) {
        expr arg = parse_expr(op.get_precedence());
        return mk_app(mk_fun(op), arg);
    }

    expr parse_postfix(expr const & left, operator_info const & op) {
        return mk_app(mk_fun(op), left);
    }

    expr parse_infix(expr const & left, operator_info const & op) {
        expr right = parse_expr(op.get_precedence()+1);
        return mk_app(mk_fun(op), left, right);
    }

    expr parse_infixl(expr const & left, operator_info const & op) {
        expr right = parse_expr(op.get_precedence());
        return mk_app(mk_fun(op), left, right);
    }

    expr parse_infixr(expr const & left, operator_info const & op) {
        expr right = parse_expr(op.get_precedence()-1);
        return mk_app(mk_fun(op), left, right);
    }

    expr parse_mixfixl(operator_info const & op) {
        not_implemented_yet();
    }

    expr parse_mixfixr(expr const & left, operator_info const & op) {
        not_implemented_yet();
    }

    expr parse_mixfixc(operator_info const & op) {
        not_implemented_yet();
    }

    expr get_name_ref(name const & id) {
        object const & obj = m_frontend.find_object(id);
        if (obj) {
            object_kind k      = obj.kind();
            if (k == object_kind::Definition || k == object_kind::Postulate)
                return mk_constant(obj.get_name());
            else
                throw parser_error("invalid object reference, object is not an expression.");
        }
        else {
            auto it = m_builtins.find(id);
            if (it != m_builtins.end()) {
                return it->second;
            } else {
                throw parser_error("unknown identifier");
            }
        }
    }

    expr parse_nud_id() {
        name id = curr_name();
        next();
        auto it = m_local_decls.find(id);
        if (it != m_local_decls.end()) {
            return mk_var(m_local_decls.size() - it->second - 1);
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
                return get_name_ref(id);
            }
        }
    }

    expr parse_led_id(expr const & left) {
        name id = curr_name();
        next();
        auto it = m_local_decls.find(id);
        if (it != m_local_decls.end()) {
            return mk_app(left, mk_var(m_local_decls.size() - it->second - 1));
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
                return mk_app(left, get_name_ref(id));
            }
        }
    }

    expr parse_lparen() {
        next();
        expr r = parse_expr();
        check_rparen_next("invalid expression, ')' expected");
        return r;
    }

    expr parse_lambda() {
        not_implemented_yet();
    }

    expr parse_pi() {
        not_implemented_yet();
    }

    expr parse_int() {
        expr r = mk_int_value(m_scanner.get_num_val().get_numerator());
        next();
        return r;
    }

    expr parse_decimal() {
        not_implemented_yet();
    }

    expr parse_string() {
        not_implemented_yet();
    }

    expr parse_type() {
        next();
        // TODO universe
        return Type();
    }

    expr parse_nud() {
        switch (curr()) {
        case scanner::token::Id:         return parse_nud_id();
        case scanner::token::LeftParen:  return parse_lparen();
        case scanner::token::Lambda:     return parse_lambda();
        case scanner::token::Pi:         return parse_pi();
        case scanner::token::IntVal:     return parse_int();
        case scanner::token::DecimalVal: return parse_decimal();
        case scanner::token::StringVal:  return parse_string();
        case scanner::token::Type:       return parse_type();
        default:
            throw parser_error("invalid expression, unexpected token");
        }
    }

    expr parse_led(expr const & left) {
        switch (curr()) {
        case scanner::token::Id:         return parse_led_id(left);
        case scanner::token::LeftParen:  return mk_app(left, parse_lparen());
        case scanner::token::IntVal:     return mk_app(left, parse_int());
        case scanner::token::DecimalVal: return mk_app(left, parse_decimal());
        case scanner::token::StringVal:  return mk_app(left, parse_string());
        case scanner::token::Type:       return mk_app(left, parse_type());
        default:                         return left;
        }
    }

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
        case scanner::token::LeftParen: case scanner::token::IntVal: case scanner::token::DecimalVal:
        case scanner::token::StringVal: case scanner::token::Type:
            return 1;
        default:
            return 0;
        }
    }

    expr parse_expr(unsigned rbp = 0) {
        expr left = parse_nud();
        while (rbp < curr_lbp()) {
            left = parse_led(left);
        }
        return left;
    }

    expr elaborate(expr const & e) {
        // TODO
        return e;
    }

    void parse_definition() {
        next();
        name id = check_identifier_next("invalid definition, identifier expected");
        check_colon_next("invalid definition, ':' expected");
        // TODO
    }

    void parse_variable() {
        next();
        name id = check_identifier_next("invalid variable declaration, identifier expected");
        check_colon_next("invalid variable declaration, ':' expected");
        expr type = elaborate(parse_expr());
        m_frontend.add_var(id, type);
    }

    void parse_theorem() {
        // TODO
    }

    void parse_axiom() {
        next();
        name id = check_identifier_next("invalid axiom, identifier expected");
        check_colon_next("invalid axiom, ':' expected");
        expr type = elaborate(parse_expr());
        m_frontend.add_axiom(id, type);
    }

    void parse_eval() {
        // TODO
    }

    void parse_show() {
        // TODO
    }

    void parse_op(fixity fx) {
        // TODO
    }

    void parse_mixfix_op(fixity fx) {
        // TODO
    }

    void parse_command() {
        name const & cmd_id = curr_name();
        if (cmd_id == g_definition_kwd)    parse_definition();
        else if (cmd_id == g_variable_kwd) parse_variable();
        else if (cmd_id == g_theorem_kwd)  parse_theorem();
        else if (cmd_id == g_axiom_kwd)    parse_axiom();
        else if (cmd_id == g_eval_kwd)     parse_eval();
        else if (cmd_id == g_show_kwd)     parse_show();
        else if (cmd_id == g_infix_kwd)    parse_op(fixity::Infix);
        else if (cmd_id == g_infixl_kwd)   parse_op(fixity::Infixl);
        else if (cmd_id == g_infixr_kwd)   parse_op(fixity::Infixr);
        else if (cmd_id == g_prefix_kwd)   parse_op(fixity::Prefix);
        else if (cmd_id == g_postfix_kwd)  parse_op(fixity::Postfix);
        else if (cmd_id == g_mixfixl_kwd)  parse_mixfix_op(fixity::Mixfixl);
        else if (cmd_id == g_mixfixr_kwd)  parse_mixfix_op(fixity::Mixfixr);
        else if (cmd_id == g_mixfixc_kwd)  parse_mixfix_op(fixity::Mixfixc);
        else { lean_unreachable(); }
    }

    void error(char const * msg, unsigned line, unsigned pos) {
        m_err << "Error (line: " << line << ", pos: " << pos << ") " << msg << std::endl;
    }

    void error(char const * msg) {
        error(msg, m_scanner.get_line(), m_scanner.get_pos());
        sync();
    }

    bool parse_commands() {
        while (true) {
            try {
                switch (curr()) {
                case scanner::token::CommandId: parse_command(); break;
                case scanner::token::Eof: return !m_found_errors;
                default:
                    throw parser_error("Command expected");
                }
            } catch (parser_error & ex) {
                m_found_errors = true;
                if (m_use_exceptions) {
                    throw parser_exception(ex.what(), m_scanner.get_line(), m_scanner.get_pos());
                } else {
                    error(ex.what());
                }
            } catch (exception & ex) {
                m_found_errors = true;
                if (m_use_exceptions) {
                    throw;
                } else {
                    error(ex.what());
                }
            }
        }
    }
};
bool parse_commands(frontend & fe, std::istream & in, std::ostream & err, bool use_exceptions) {
    return parser_fn(fe, in, err, use_exceptions).parse_commands();
}
}

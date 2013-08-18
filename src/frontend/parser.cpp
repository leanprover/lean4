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
#include "normalize.h"
#include "type_check.h"
#include "free_vars.h"
#include "builtin_notation.h"
#include "builtin.h"
#include "arith.h"
#include "pp.h"
#include "printer.h"

namespace lean {
static name g_definition_kwd("Definition");
static name g_variable_kwd("Variable");
static name g_theorem_kwd("Theorem");
static name g_axiom_kwd("Axiom");
static name g_universe_kwd("Universe");
static name g_eval_kwd("Eval");
static name g_show_kwd("Show");
static name g_check_kwd("Check");
static name g_env_kwd("Environment");
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

static list<name> g_command_keywords = {g_definition_kwd, g_variable_kwd, g_theorem_kwd, g_axiom_kwd, g_universe_kwd, g_eval_kwd, g_show_kwd, g_check_kwd, g_env_kwd, g_infix_kwd, g_infixl_kwd, g_infixr_kwd, g_prefix_kwd, g_postfix_kwd, g_mixfixl_kwd, g_mixfixr_kwd, g_mixfixc_kwd};

/** \brief Functional object for parsing */
struct parser_fn {
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef std::unordered_map<name, expr, name_hash, name_eq>  builtins;
    frontend       m_frontend;
    scanner        m_scanner;
    formatter      m_formatter;
    std::ostream * m_out;
    std::ostream * m_err;
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
    mpq const & curr_num() const { return m_scanner.get_num_val(); }

    void check_next(scanner::token t, char const * msg) {
        if (curr() == t)
            next();
        else
            throw parser_error(msg);
    }

    bool curr_is_identifier() const { return curr() == scanner::token::Id; }
    bool curr_is_lparen() const { return curr() == scanner::token::LeftParen; }
    bool curr_is_colon() const { return curr() == scanner::token::Colon; }
    bool curr_is_comma() const { return curr() == scanner::token::Comma; }
    bool curr_is_in() const { return curr() == scanner::token::In; }

    void check_identifier(char const * msg) { if (!curr_is_identifier()) throw parser_error(msg); }
    name check_identifier_next(char const * msg) { check_identifier(msg); name r = curr_name(); next(); return r; }
    void check_colon_next(char const * msg) { check_next(scanner::token::Colon, msg); }
    void check_comma_next(char const * msg) { check_next(scanner::token::Comma, msg); }
    void check_lparen_next(char const * msg) { check_next(scanner::token::LeftParen, msg); }
    void check_rparen_next(char const * msg) { check_next(scanner::token::RightParen, msg); }
    void check_assign_next(char const * msg) { check_next(scanner::token::Assign, msg); }
    void check_name(name const & op, char const * msg) { if(!curr_is_identifier() || curr_name() != op) throw parser_error(msg); }
    void check_name_next(name const & op, char const * msg) { check_name(op, msg); next(); }

    void init_builtins() {
        m_builtins["Bool"]   = Bool;
        m_builtins["true"]   = True;
        m_builtins["false"]  = False;
        m_builtins["\u22A4"] = True;
        m_builtins["\u22A5"] = False;
        m_builtins["Int"]    = Int;
    }

    parser_fn(frontend & fe, std::istream & in, std::ostream * out, std::ostream * err, bool use_exceptions):
        m_frontend(fe),
        m_scanner(in),
        m_formatter(mk_pp_formatter(fe)),
        m_out(out),
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

    void check_op_part(name const & op_part) {
        check_name_next(op_part, "invalid expression, identifier expected");
    }

    void parse_mixfix_args(list<name> const & ops, unsigned prec, buffer<expr> & args) {
        auto it = ops.begin();
        ++it;
        while (it != ops.end()) {
            check_op_part(*it);
            args.push_back(parse_expr(prec));
            ++it;
        }
    }

    expr parse_mixfixl(operator_info const & op) {
        buffer<expr> args;
        args.push_back(mk_fun(op));
        args.push_back(parse_expr(op.get_precedence()));
        parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
        return mk_app(args.size(), args.data());
    }

    expr parse_mixfixr(expr const & left, operator_info const & op) {
        buffer<expr> args;
        args.push_back(mk_fun(op));
        args.push_back(left);
        parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
        return mk_app(args.size(), args.data());
    }

    expr parse_mixfixc(operator_info const & op) {
        buffer<expr> args;
        args.push_back(mk_fun(op));
        args.push_back(parse_expr(op.get_precedence()));
        list<name> const & ops = op.get_op_name_parts();
        auto it = ops.begin();
        ++it;
        while (true) {
            check_op_part(*it);
            ++it;
            if (it == ops.end())
                return mk_app(args.size(), args.data());
            args.push_back(parse_expr(op.get_precedence()));
        }
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

    expr parse_eq(expr const & left) {
        next();
        expr right = parse_expr(g_eq_precedence);
        return mk_eq(left, right);
    }

    expr parse_lparen() {
        next();
        expr r = parse_expr();
        check_rparen_next("invalid expression, ')' expected");
        return r;
    }

    void parse_names(buffer<name> & result) {
        while (curr_is_identifier()) {
            result.push_back(curr_name());
            next();
        }
    }

    void register_binding(name const & n) {
        m_local_decls.insert(n, m_local_decls.size());
    }

    void parse_simple_bindings(buffer<std::pair<name, expr>> & result) {
        // ID ... ID : type
        buffer<name> names;
        parse_names(names);
        check_colon_next("invalid binder, ':' expected");
        unsigned sz = result.size();
        result.resize(sz + names.size());
        expr type = parse_expr();
        for (name const & n : names) register_binding(n);
        unsigned i = names.size();
        while (i > 0) {
            --i;
            result[sz + i] = mk_pair(names[i], lift_free_vars(type, i));
        }
    }

    void parse_bindings(buffer<std::pair<name, expr>> & result) {
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

    expr mk_abstraction(bool is_lambda, buffer<std::pair<name, expr>> const & bindings, expr const & body) {
        expr result = body;
        unsigned i = bindings.size();
        while (i > 0) {
            --i;
            if (is_lambda)
                result = mk_lambda(bindings[i].first, bindings[i].second, result);
            else
                result = mk_pi(bindings[i].first, bindings[i].second, result);
        }
        return result;
    }

    expr parse_abstraction(bool is_lambda) {
        next();
        local_decls::mk_scope scope(m_local_decls);
        buffer<std::pair<name, expr>> bindings;
        parse_bindings(bindings);
        check_comma_next("invalid abstraction, ',' expected");
        expr result = parse_expr();
        return mk_abstraction(is_lambda, bindings, result);
    }

    expr parse_lambda() {
        return parse_abstraction(true);
    }

    expr parse_pi() {
        return parse_abstraction(false);
    }

    expr parse_let() {
        next();
        local_decls::mk_scope scope(m_local_decls);
        buffer<std::pair<name, expr>> bindings;
        while (true) {
            name id  = check_identifier_next("invalid let expression, identifier expected");
            check_assign_next("invalid let expression, ':=' expected");
            expr val = parse_expr();
            register_binding(id);
            bindings.push_back(mk_pair(id, val));
            if (curr_is_in()) {
                next();
                expr r = parse_expr();
                unsigned i = bindings.size();
                while (i > 0) {
                    --i;
                    r = mk_let(bindings[i].first, bindings[i].second, r);
                }
                return r;
            } else {
                check_comma_next("invalid let expression, ',' or 'in' expected");
            }
        }
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
        case scanner::token::Let:        return parse_let();
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
        case scanner::token::Eq:         return parse_eq(left);
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
        case scanner::token::Eq : return g_eq_precedence;
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
            local_decls::mk_scope scope(m_local_decls);
            buffer<std::pair<name, expr>> bindings;
            parse_bindings(bindings);
            check_colon_next("invalid definition, ':' expected");
            expr type_body = parse_expr();
            check_assign_next("invalid definition, ':=' expected");
            expr val_body  = parse_expr();
            type = elaborate(mk_abstraction(false, bindings, type_body));
            val  = elaborate(mk_abstraction(true, bindings, val_body));
        }
        if (is_definition)
            m_frontend.add_definition(id, type, val);
        else
            m_frontend.add_theorem(id, type, val);
    }

    void parse_definition() {
        parse_def_core(true);
    }

    void parse_theorem() {
        parse_def_core(false);
    }

    void parse_variable() {
        next();
        name id = check_identifier_next("invalid variable declaration, identifier expected");
        check_colon_next("invalid variable declaration, ':' expected");
        expr type = elaborate(parse_expr());
        m_frontend.add_var(id, type);
    }

    void parse_axiom() {
        next();
        name id = check_identifier_next("invalid axiom, identifier expected");
        check_colon_next("invalid axiom, ':' expected");
        expr type = elaborate(parse_expr());
        m_frontend.add_axiom(id, type);
    }

    void parse_eval() {
        next();
        expr v = elaborate(parse_expr());
        expr r = normalize(v, m_frontend);
        (*m_out) << m_formatter(r) << std::endl;
    }

    void parse_show() {
        next();
        expr v = elaborate(parse_expr());
        (*m_out) << m_formatter(v) << std::endl;
    }

    void parse_check() {
        next();
        expr v = elaborate(parse_expr());
        expr t = infer_type(v, m_frontend);
        (*m_out) << m_formatter(t) << std::endl;
    }

    void parse_env() {
        next();
        (*m_out) << m_frontend << std::endl;
    }

    unsigned parse_precision() {
        if (curr() == scanner::token::IntVal) {
            mpz pval = curr_num().get_numerator();
            if (!pval.is_unsigned_int())
                throw parser_error("invalid operator definition, precedence does not fit in a machine integer");
            unsigned r = pval.get_unsigned_int();
            next();
            return r;
        } else {
            return 0;
        }
    }

    name parse_op_id() {
        return check_identifier_next("invalid operator definition, identifier expected");
    }

    void parse_op(fixity fx) {
        next();
        unsigned prec = parse_precision();
        name op_id = parse_op_id();
        name id    = parse_op_id();
        switch (fx) {
        case fixity::Prefix:  m_frontend.add_prefix(op_id, prec, id); break;
        case fixity::Postfix: m_frontend.add_postfix(op_id, prec, id); break;
        case fixity::Infix:   m_frontend.add_infix(op_id, prec, id); break;
        case fixity::Infixl:  m_frontend.add_infixl(op_id, prec, id); break;
        case fixity::Infixr:  m_frontend.add_infixr(op_id, prec, id); break;
        default: lean_unreachable(); break;
        }
    }

    void parse_mixfix_op(fixity fx) {
        next();
        unsigned prec = parse_precision();
        buffer<name> parts;
        parts.push_back(parse_op_id());
        parts.push_back(parse_op_id());
        name id = parse_op_id();
        while (curr_is_identifier()) {
            parts.push_back(id);
            id = curr_name();
            next();
        }
        switch (fx) {
        case fixity::Mixfixl:  m_frontend.add_mixfixl(parts.size(), parts.data(), prec, id); break;
        case fixity::Mixfixr:  m_frontend.add_mixfixr(parts.size(), parts.data(), prec, id); break;
        case fixity::Mixfixc:  m_frontend.add_mixfixc(parts.size(), parts.data(), prec, id); break;
        default: lean_unreachable(); break;
        }
    }

    void parse_command() {
        name const & cmd_id = curr_name();
        if (cmd_id == g_definition_kwd)    parse_definition();
        else if (cmd_id == g_variable_kwd) parse_variable();
        else if (cmd_id == g_theorem_kwd)  parse_theorem();
        else if (cmd_id == g_axiom_kwd)    parse_axiom();
        else if (cmd_id == g_eval_kwd)     parse_eval();
        else if (cmd_id == g_show_kwd)     parse_show();
        else if (cmd_id == g_check_kwd)    parse_check();
        else if (cmd_id == g_env_kwd)      parse_env();
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
        lean_assert(m_err);
        (*m_err) << "Error (line: " << line << ", pos: " << pos << ") " << msg << std::endl;
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
                case scanner::token::Period: next(); break;
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

    expr parse_expr_main() {
        try {
            return elaborate(parse_expr());
        } catch (parser_error & ex) {
            throw parser_exception(ex.what(), m_scanner.get_line(), m_scanner.get_pos());
        }
    }

};
bool parse_commands(frontend & fe, std::istream & in, std::ostream & out, std::ostream & err, bool use_exceptions) {
    return parser_fn(fe, in, &out, &err, use_exceptions).parse_commands();
}
expr parse_expr(frontend const & fe, std::istream & in) {
    return parser_fn(const_cast<frontend&>(fe), in, nullptr, nullptr, true).parse_expr_main();
}
}

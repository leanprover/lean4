/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <utility>
#include <string>
#include <vector>
#include "util/flet.h"
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/free_vars.h"
#include "kernel/builtin.h"
#include "library/placeholder.h"
#include "library/io_state_stream.h"
#include "library/arith/nat.h"
#include "library/arith/int.h"
#include "library/arith/real.h"
#include "frontends/lean/parser_imp.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/notation.h"
#include "frontends/lean/parser_calc.h"

namespace lean {
// A name that can't be created by the user.
// It is used as placeholder for parsing A -> B expressions which
// are syntax sugar for (Pi (_ : A), B)
static name g_unused = name::mk_internal_unique_name();
static name g_calc("calc");

/**
   \brief Return the size of the implicit vector associated with the given denotation.
*/
unsigned parser_imp::get_implicit_vector_size(expr const & d) {
    return get_implicit_arguments(m_env, d).size();
}

/**
   \brief Return a vector \c v that is the implicit vector for some \c d in \c ds,
   and <tt>v.size() == min{get_implicit_vector_size(d) | d in ds}</tt>
*/
std::vector<bool> const & parser_imp::get_smallest_implicit_vector(list<expr> const & ds) {
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
unsigned parser_imp::get_smallest_implicit_vector_size(list<expr> const & ds) {
    return get_smallest_implicit_vector(ds).size();
}

/**
   \brief Return the function associated with the given operator.
   If the operator has been overloaded, it returns a choice expression
   of the form <tt>(choice f_1 f_2 ... f_k)</tt> where f_i's are different options.
   After we finish parsing, the elaborator
   resolve/decide which f_i should be used.
*/
expr parser_imp::mk_fun(operator_info const & op, pos_info const & pos) {
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
expr parser_imp::mk_application(operator_info const & op, pos_info const & pos, unsigned num_args, expr const * args) {
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

expr parser_imp::mk_application(operator_info const & op, pos_info const & pos, std::initializer_list<expr> const & l) {
    return mk_application(op, pos, l.size(), l.begin());
}
expr parser_imp::mk_application(operator_info const & op, pos_info const & pos, expr const & arg) {
    return mk_application(op, pos, 1, &arg);
}
expr parser_imp::mk_application(operator_info const & op, pos_info const & pos, buffer<expr> const & args) {
    return mk_application(op, pos, args.size(), args.data());
}

/** \brief Parse a user defined prefix operator. */
expr parser_imp::parse_prefix(operator_info const & op) {
    auto p = pos();
    return mk_application(op, p, parse_expr(op.get_precedence()));
}

/** \brief Parse a user defined postfix operator. */
expr parser_imp::parse_postfix(expr const & left, operator_info const & op, pos_info const & op_pos) {
    return mk_application(op, op_pos, left);
}

/** \brief Parse a user defined infix operator. */
expr parser_imp::parse_infix(expr const & left, operator_info const & op, pos_info const & op_pos) {
    return mk_application(op, op_pos, {left, parse_expr(op.get_precedence()+1)});
}

/** \brief Parse a user defined infix-left operator. */
expr parser_imp::parse_infixl(expr const & left, operator_info const & op, pos_info const & op_pos) {
    return mk_application(op, op_pos, {left, parse_expr(op.get_precedence())});
}

/** \brief Parse a user defined infix-right operator. */
expr parser_imp::parse_infixr(expr const & left, operator_info const & op, pos_info const & op_pos) {
    return mk_application(op, op_pos, {left, parse_expr(op.get_precedence()-1)});
}

/**
   \brief Throws an error if the current token is not an identifier named \c op_part.
   If it is, move to the next toke. The error message assumes
   this method has been used when parsing mixfix operators.
*/
void parser_imp::check_op_part(name const & op_part) {
    if (!curr_is_identifier() || curr_name() != op_part)
        throw parser_error(sstream() << "invalid mixfix operator application, '" << op_part << "' expected", pos());
    next();
}

/**
   \brief Auxiliary function for #parse_mixfixl and #parse_mixfixo

   It parses (ID _)*
*/
void parser_imp::parse_mixfix_args(list<name> const & ops, unsigned prec, buffer<expr> & args) {
    auto it = ops.begin();
    ++it;
    while (it != ops.end()) {
        check_op_part(*it);
        args.push_back(parse_expr(prec));
        ++it;
    }
}

/** \brief Parse user defined mixfixl operator. It has the form: ID _ ... ID _ */
expr parser_imp::parse_mixfixl(operator_info const & op) {
    auto p = pos();
    buffer<expr> args;
    args.push_back(parse_expr(op.get_precedence()));
    parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
    return mk_application(op, p, args);
}

/** \brief Parse user defined mixfixr operator. It has the form: _ ID ... _ ID */
expr parser_imp::parse_mixfixr(expr const & left, operator_info const & op, pos_info const & op_pos) {
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
    return mk_application(op, op_pos, args);
}

/** \brief Parse user defined mixfixr operator. It has the form: _ ID ... _ ID _ */
expr parser_imp::parse_mixfixo(expr const & left, operator_info const & op, pos_info const & op_pos) {
    buffer<expr> args;
    args.push_back(left);
    args.push_back(parse_expr(op.get_precedence()));
    parse_mixfix_args(op.get_op_name_parts(), op.get_precedence(), args);
    return mk_application(op, op_pos, args);
}

/** \brief Parse user defined mixfixc operator. It has the form: ID _ ID ... _ ID */
expr parser_imp::parse_mixfixc(operator_info const & op) {
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

expr parser_imp::get_name_ref(name const & id, pos_info const & p, bool implicit_args) {
    auto it = m_using_decls.find(id);
    if (it != m_using_decls.end()) {
        return it->second;
    } else {
        lean_assert(!m_namespace_prefixes.empty());
        auto it    = m_namespace_prefixes.end();
        auto begin = m_namespace_prefixes.begin();
        while (it != begin) {
            --it;
            name nid = *it + id;
            optional<object> obj = m_env->find_object(nid);
            if (obj) {
                object_kind k      = obj->kind();
                if (k == object_kind::Definition || k == object_kind::Postulate || k == object_kind::Builtin) {
                    if (implicit_args && has_implicit_arguments(m_env, obj->get_name())) {
                        std::vector<bool> const & imp_args = get_implicit_arguments(m_env, obj->get_name());
                        buffer<expr> args;
                        pos_info p = pos();
                        expr f = mk_constant(obj->get_name());
                        args.push_back(save(f, p));
                        for (unsigned i = 0; i < imp_args.size(); i++) {
                            if (imp_args[i]) {
                                args.push_back(save(mk_placeholder(), pos()));
                            } else {
                                args.push_back(parse_expr(g_app_precedence));
                            }
                        }
                        return mk_app(args);
                    } else {
                        return mk_constant(obj->get_name());
                    }
                } else {
                    throw parser_error(sstream() << "invalid object reference, object '" << nid << "' is not an expression.", p);
                }
            } else if (!m_check_identifiers) {
                return mk_constant(nid);
            }
        }
    }
    throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
}

void parser_imp::propagate_position(expr const & e, pos_info p) {
    for_each(e, [&](expr const & e, unsigned) {
            if (m_expr_pos_info.find(e) == m_expr_pos_info.end()) {
                save(e, p);
                return true;
            } else {
                return false; // do not search children...
            }
        });
}

bool parser_imp::is_curr_begin_expr() const {
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

bool parser_imp::is_curr_begin_tactic() const {
    switch (curr()) {
    case scanner::token::LeftParen: case scanner::token::Id:    return true;
    default:                                                    return false;
    }
}

/**
   \brief Parse a macro implemented in Lua
*/
parser_imp::macro_result parser_imp::parse_macro(list<macro_arg_kind> const & arg_kinds, luaref const & fn, unsigned prec, macro_arg_stack & args,
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
        case macro_arg_kind::Parameters: {
            mk_scope scope(*this);
            parameter_buffer parameters;
            parse_expr_parameters(parameters);
            args.emplace_back(k, &parameters);
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
                    case macro_arg_kind::Parameters: {
                        parameter_buffer const & parameters = *static_cast<parameter_buffer*>(arg);
                        lua_newtable(L);
                        int i = 1;
                        for (auto const & p : parameters) {
                            lua_newtable(L);
                            push_name(L, p.m_name);
                            lua_rawseti(L, -2, 1);
                            push_expr(L, p.m_type);
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

expr parser_imp::parse_expr_macro(name const & id, pos_info const & p) {
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

expr parser_imp::parse_calc() {
    return get_calc_proof_parser().parse(*this);
}

/**
   \brief Parse an identifier that has a "null denotation" (See
   paper: "Top down operator precedence"). A nud identifier is a
   token that appears at the beginning of a language construct.
   In Lean, local declarations (i.e., local functions), user
   defined prefix, mixfixl and mixfixc operators, and global
   functions can begin a language construct.
*/
expr parser_imp::parse_nud_id() {
    auto p = pos();
    name id = curr_name();
    next();
    auto it = m_local_decls.find(id);
    if (it != m_local_decls.end()) {
        return save(mk_var(m_num_local_decls - it->second - 1), p);
    } else if (m_expr_macros && m_expr_macros->find(id) != m_expr_macros->end()) {
        return parse_expr_macro(id, p);
    } else if (auto alias = get_alias(m_env, id)) {
        return save(*alias, p);
    } else if (id == g_calc) {
        return parse_calc();
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
expr parser_imp::parse_led_id(expr const & left) {
    auto p  = pos();
    auto p2 = pos_of(left, p);
    name id = curr_name();
    next();
    auto it = m_local_decls.find(id);
    if (it != m_local_decls.end()) {
        return save(mk_app(left, save(mk_var(m_num_local_decls - it->second - 1), p)), p2);
    } else if (m_expr_macros && m_expr_macros->find(id) != m_expr_macros->end()) {
        return save(mk_app(left, parse_expr_macro(id, p)), p2);
    } else if (auto alias = get_alias(m_env, id)) {
        return save(mk_app(left, save(*alias, p)), p2);
    } else if (id == g_calc) {
        return save(mk_app(left, parse_calc()), p2);
    } else {
        operator_info op = find_led(m_env, id);
        if (op) {
            switch (op.get_fixity()) {
            case fixity::Infix:   return parse_infix(left, op, p);
            case fixity::Infixl:  return parse_infixl(left, op, p);
            case fixity::Infixr:  return parse_infixr(left, op, p);
            case fixity::Mixfixr: return parse_mixfixr(left, op, p);
            case fixity::Mixfixo: return parse_mixfixo(left, op, p);
            case fixity::Postfix: return parse_postfix(left, op, p);
            default: lean_unreachable(); // LCOV_EXCL_LINE
            }
        } else {
            return save(mk_app(left, save(get_name_ref(id, p), p)), p2);
        }
    }
}

/** \brief Parse <tt>expr '=' expr</tt>. */
expr parser_imp::parse_heq(expr const & left) {
    auto p = pos();
    next();
    expr right = parse_expr(g_eq_precedence);
    return save(mk_heq(left, right), p);
}

/** \brief Parse <tt>expr '->' expr</tt>. */
expr parser_imp::parse_arrow(expr const & left) {
    auto p = pos();
    next();
    mk_scope scope(*this);
    register_binding(g_unused);
    // The -1 is a trick to get right associativity in Pratt's parsers
    expr right = parse_expr(g_arrow_precedence-1);
    return save(mk_arrow(left, right), p);
}

/** \brief Parse <tt>'(' expr ')'</tt>. */
expr parser_imp::parse_lparen() {
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
void parser_imp::parse_names(buffer<std::pair<pos_info, name>> & result) {
    while (curr_is_identifier()) {
        result.emplace_back(pos(), curr_name());
        next();
    }
}

/** \brief Register the name \c n as a local declaration. */
void parser_imp::register_binding(name const & n) {
    unsigned lvl = m_num_local_decls;
    m_local_decls.insert(n, lvl);
    m_num_local_decls++;
    lean_assert(m_local_decls.find(n)->second == lvl);
}

/**
   \brief Parse <tt>ID ... ID ':' expr</tt>, where the expression
   represents the type of the identifiers.

   \remark If \c implicit_decl is true, then the parameters should be
   marked as implicit. This flag is set to true, for example,
   when we are parsing definitions such as:
   <code> Definition f {A : Type} (a b : A), A := ... </code>
   The <code>{A : Type}</code> is considered an implicit argument declaration.

   \remark If \c suppress_type is true, then the type doesn't
   need to be provided. That is, we automatically include a placeholder.
*/
void parser_imp::parse_simple_parameters(parameter_buffer & result, bool implicit_decl, bool suppress_type) {
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
        result[sz + i] = parameter(names[i].first, names[i].second, arg_type, implicit_decl);
    }
}

void parser_imp::parse_parameters(parameter_buffer & result, bool implicit_decls, bool suppress_type) {
    if (curr_is_identifier()) {
        parse_simple_parameters(result, false, suppress_type);
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
        parse_simple_parameters(result, implicit, suppress_type);
        if (!implicit)
            check_rparen_next("invalid binder, ')' expected");
        else
            check_rcurly_next("invalid binder, '}' expected");
        while (curr_is_lparen() || (implicit_decls && curr_is_lcurly())) {
            bool implicit = curr_is_lcurly();
            next();
            parse_simple_parameters(result, implicit, suppress_type);
            if (!implicit)
                check_rparen_next("invalid binder, ')' expected");
            else
                check_rcurly_next("invalid binder, '}' expected");
        }
    }
}

void parser_imp::parse_expr_parameters(parameter_buffer & result) {
    parse_parameters(result, false, true);
}

void parser_imp::parse_var_decl_parameters(parameter_buffer & result) {
    parse_parameters(result, true, false);
}

void parser_imp::parse_definition_parameters(parameter_buffer & result) {
    parse_parameters(result, true, true);
}

/**
   \brief Create a lambda/Pi abstraction, using the giving binders
   and body.
*/
expr parser_imp::mk_abstraction(bool is_lambda, parameter_buffer const & parameters, expr const & body) {
    expr result = body;
    unsigned i = parameters.size();
    while (i > 0) {
        --i;
        pos_info p = parameters[i].m_pos;
        if (is_lambda)
            result = save(mk_lambda(parameters[i].m_name, parameters[i].m_type, result), p);
        else
            result = save(mk_pi(parameters[i].m_name, parameters[i].m_type, result), p);
    }
    return result;
}

/** \brief Parse lambda/Pi abstraction. */
expr parser_imp::parse_abstraction(bool is_lambda) {
    next();
    mk_scope scope(*this);
    parameter_buffer parameters;
    parse_expr_parameters(parameters);
    check_comma_next("invalid abstraction, ',' expected");
    expr result = parse_expr();
    return mk_abstraction(is_lambda, parameters, result);
}

/** \brief Parse lambda abstraction. */
expr parser_imp::parse_lambda() {
    return parse_abstraction(true);
}

/** \brief Parse Pi abstraction. */
expr parser_imp::parse_pi() {
    return parse_abstraction(false);
}

/** \brief Parse exists */
expr parser_imp::parse_exists() {
    next();
    mk_scope scope(*this);
    parameter_buffer parameters;
    parse_expr_parameters(parameters);
    check_comma_next("invalid exists, ',' expected");
    expr result = parse_expr();
    unsigned i = parameters.size();
    while (i > 0) {
        --i;
        pos_info p = parameters[i].m_pos;
        expr lambda = save(mk_lambda(parameters[i].m_name, parameters[i].m_type, result), p);
        result = save(mk_exists(parameters[i].m_type, lambda), p);
    }
    return result;
}

/** \brief Parse Let expression. */
expr parser_imp::parse_let() {
    next();
    mk_scope scope(*this);
    buffer<std::tuple<pos_info, name, optional<expr>, expr>> parameters;
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
        parameters.emplace_back(p, id, type, val);
        if (curr_is_in()) {
            next();
            expr r = parse_expr();
            unsigned i = parameters.size();
            while (i > 0) {
                --i;
                auto p = std::get<0>(parameters[i]);
                r = save(mk_let(std::get<1>(parameters[i]), std::get<2>(parameters[i]), std::get<3>(parameters[i]), r), p);
            }
            return r;
        } else {
            check_comma_next("invalid let expression, ',' or 'in' expected");
        }
    }
}

/** \brief Parse a natural/integer number value. */
expr parser_imp::parse_nat_int() {
    auto p = pos();
    mpz v  = m_scanner.get_num_val().get_numerator();
    expr r = v >= 0 ? mk_nat_value(v) : mk_int_value(v);
    r = save(r, p);
    next();
    return r;
}

expr parser_imp::parse_decimal() {
    auto p = pos();
    expr r = save(mk_real_value(m_scanner.get_num_val()), p);
    next();
    return r;
}

expr parser_imp::parse_string() {
    // TODO(Leo)
    not_implemented_yet();
}

/** \brief Parse <tt>'Type'</tt> and <tt>'Type' level</tt> expressions. */
expr parser_imp::parse_type(bool level_expected) {
    auto p = pos();
    next();
    if (level_expected) {
        return save(mk_type(parse_level()), p);
    } else {
        return save(Type(), p);
    }
}

/** \brief Parse \c _ a hole that must be filled by the elaborator. */
expr parser_imp::parse_placeholder() {
    auto p = pos();
    next();
    return save(mk_placeholder(), p);
}

tactic parser_imp::parse_tactic_macro(name tac_id, pos_info const & p) {
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
tactic parser_imp::parse_tactic_expr() {
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

static name g_have_expr("have_expr");

/** \brief Parse <tt>'have' expr 'by' tactic</tt> and <tt>'have' expr ':' expr</tt> */
expr parser_imp::parse_have_expr() {
    auto p = pos();
    next();
    expr t = parse_expr();
    if (curr_is_colon()) {
        next();
        expr b = parse_expr();
        return mk_let(g_have_expr, t, b, Var(0));
    } else {
        check_next(scanner::token::By, "invalid 'have' expression, 'by' or ':' expected");
        tactic tac = parse_tactic_expr();
        expr r = mk_placeholder(some_expr(t));
        m_tactic_hints.insert(mk_pair(r, tac));
        return save(r, p);
    }
}

/** \brief Parse <tt>'by' tactic</tt> */
expr parser_imp::parse_by_expr() {
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
expr parser_imp::parse_nud() {
    switch (curr()) {
    case scanner::token::Id:          return parse_nud_id();
    case scanner::token::LeftParen:   return parse_lparen();
    case scanner::token::Lambda:      return parse_lambda();
    case scanner::token::Pi:          return parse_pi();
    case scanner::token::Exists:      return parse_exists();
    case scanner::token::Let:         return parse_let();
    case scanner::token::IntVal:      return parse_nat_int();
    case scanner::token::DecimalVal:  return parse_decimal();
    case scanner::token::StringVal:   return parse_string();
    case scanner::token::Placeholder: return parse_placeholder();
    case scanner::token::Type:        return parse_type(false);
    case scanner::token::Have:        return parse_have_expr();
    case scanner::token::By:          return parse_by_expr();
    default:
        throw parser_error("invalid expression, unexpected token", pos());
    }
}

/**
   \brief Create a new application and associate position of left with the resultant expression.
*/
expr parser_imp::mk_app_left(expr const & left, expr const & arg) {
    if (is_type(left))
        throw parser_error("Type is not a function, use '(Type <universe>)' for specifying a particular type universe", pos());
    auto it = m_expr_pos_info.find(left);
    lean_assert(it != m_expr_pos_info.end());
    return save(mk_app(left, arg), it->second);
}

/**
   \brief Auxiliary method used when processing the 'inside' of an expression.
*/
expr parser_imp::parse_led(expr const & left) {
    switch (curr()) {
    case scanner::token::Id:          return parse_led_id(left);
    case scanner::token::Eq:          return parse_heq(left);
    case scanner::token::Arrow:       return parse_arrow(left);
    case scanner::token::LeftParen:   return mk_app_left(left, parse_lparen());
    case scanner::token::IntVal:      return mk_app_left(left, parse_nat_int());
    case scanner::token::DecimalVal:  return mk_app_left(left, parse_decimal());
    case scanner::token::StringVal:   return mk_app_left(left, parse_string());
    case scanner::token::Placeholder: return mk_app_left(left, parse_placeholder());
    case scanner::token::Type:        return mk_app_left(left, parse_type(false));
    default:                          return left;
    }
}

/** \brief Return the binding power of the current token (when parsing expression). */
unsigned parser_imp::curr_lbp() {
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
    case scanner::token::LeftParen: case scanner::token::IntVal: case scanner::token::DecimalVal:
    case scanner::token::StringVal: case scanner::token::Type: case scanner::token::Placeholder:
        return g_app_precedence;
    default:
        return 0;
    }
}

/** \brief Parse an expression */
expr parser_imp::parse_expr(unsigned rbp) {
    expr left = parse_nud();
    while (rbp < curr_lbp()) {
        left = parse_led(left);
    }
    return left;
}
}

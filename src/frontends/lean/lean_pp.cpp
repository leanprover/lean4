/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <memory>
#include "context.h"
#include "scoped_map.h"
#include "for_each.h"
#include "instantiate.h"
#include "occurs.h"
#include "builtin.h"
#include "free_vars.h"
#include "context_to_lambda.h"
#include "options.h"
#include "interruptable_ptr.h"
#include "exception.h"
#include "lean_notation.h"
#include "lean_pp.h"
#include "lean_frontend.h"

#ifndef LEAN_DEFAULT_PP_MAX_DEPTH
#define LEAN_DEFAULT_PP_MAX_DEPTH std::numeric_limits<unsigned>::max()
#endif

#ifndef LEAN_DEFAULT_PP_MAX_STEPS
#define LEAN_DEFAULT_PP_MAX_STEPS std::numeric_limits<unsigned>::max()
#endif

#ifndef LEAN_DEFAULT_PP_IMPLICIT
#define LEAN_DEFAULT_PP_IMPLICIT false
#endif

#ifndef LEAN_DEFAULT_PP_NOTATION
#define LEAN_DEFAULT_PP_NOTATION true
#endif

#ifndef LEAN_DEFAULT_PP_EXTRA_LETS
#define LEAN_DEFAULT_PP_EXTRA_LETS true
#endif

#ifndef LEAN_DEFAULT_PP_ALIAS_MIN_WEIGHT
#define LEAN_DEFAULT_PP_ALIAS_MIN_WEIGHT 20
#endif

namespace lean {
static format g_Type_fmt      = highlight_builtin(format("Type"));
static format g_eq_fmt        = format("=");
static format g_lambda_n_fmt  = highlight_keyword(format("\u03BB"));
static format g_Pi_n_fmt      = highlight_keyword(format("\u03A0"));
static format g_lambda_fmt    = highlight_keyword(format("fun"));
static format g_Pi_fmt        = highlight_keyword(format("Pi"));
static format g_arrow_n_fmt   = highlight_keyword(format("\u2192"));
static format g_arrow_fmt     = highlight_keyword(format("->"));
static format g_forall_n_fmt  = highlight_keyword(format("\u2200"));
static format g_exists_n_fmt  = highlight_keyword(format("\u2203"));
static format g_forall_fmt    = highlight_keyword(format("forall"));
static format g_exists_fmt    = highlight_keyword(format("exists"));
static format g_ellipsis_n_fmt= highlight(format("\u2026"));
static format g_ellipsis_fmt  = highlight(format("..."));
static format g_let_fmt       = highlight_keyword(format("let"));
static format g_in_fmt        = highlight_keyword(format("in"));
static format g_assign_fmt    = highlight_keyword(format(":="));
static format g_geq_fmt       = format("\u2265");

static name g_pp_max_depth       {"lean", "pp", "max_depth"};
static name g_pp_max_steps       {"lean", "pp", "max_steps"};
static name g_pp_implicit        {"lean", "pp", "implicit"};
static name g_pp_notation        {"lean", "pp", "notation"};
static name g_pp_extra_lets      {"lean", "pp", "extra_lets"};
static name g_pp_alias_min_weight{"lean", "pp", "alias_min_weight"};

RegisterUnsignedOption(g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH, "(lean pretty printer) maximum expression depth, after that it will use ellipsis");
RegisterUnsignedOption(g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS, "(lean pretty printer) maximum number of visited expressions, after that it will use ellipsis");
RegisterBoolOption(g_pp_implicit,  LEAN_DEFAULT_PP_IMPLICIT, "(lean pretty printer) display implicit parameters");
RegisterBoolOption(g_pp_notation,  LEAN_DEFAULT_PP_NOTATION, "(lean pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)");
RegisterBoolOption(g_pp_extra_lets,  LEAN_DEFAULT_PP_EXTRA_LETS, "(lean pretty printer) introduce extra let expressions when displaying shared terms");
RegisterUnsignedOption(g_pp_alias_min_weight,  LEAN_DEFAULT_PP_ALIAS_MIN_WEIGHT, "(lean pretty printer) mimimal weight (approx. size) of a term to be considered a shared term");

unsigned get_pp_max_depth(options const & opts)        { return opts.get_unsigned(g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH); }
unsigned get_pp_max_steps(options const & opts)        { return opts.get_unsigned(g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS); }
bool     get_pp_implicit(options const & opts)         { return opts.get_bool(g_pp_implicit, LEAN_DEFAULT_PP_IMPLICIT); }
bool     get_pp_notation(options const & opts)         { return opts.get_bool(g_pp_notation, LEAN_DEFAULT_PP_NOTATION); }
bool     get_pp_extra_lets(options const & opts)       { return opts.get_bool(g_pp_extra_lets, LEAN_DEFAULT_PP_EXTRA_LETS); }
unsigned get_pp_alias_min_weight(options const & opts) { return opts.get_unsigned(g_pp_alias_min_weight, LEAN_DEFAULT_PP_ALIAS_MIN_WEIGHT); }

// =======================================
// Prefixes for naming aliases (auxiliary local decls)
static name g_kappa("\u03BA");
static name g_pho("\u03C1");
static name g_nu("\u03BD");
// =======================================

/**
   \brief Return a fresh name for the given abstraction or let.
   By fresh, we mean a name that is not used for any constant in abst_body(e).
   The resultant name is based on abst_name(e).
*/
name get_unused_name(expr const & e) {
    name const & n = is_abstraction(e) ? abst_name(e) : let_name(e);
    name n1    = n;
    unsigned i = 1;
    expr const & b = is_abstraction(e) ? abst_body(e) : let_body(e);
    while (occurs(n1, b)) {
        n1 = name(n, i);
        i++;
    }
    return n1;
}

/** \brief Functional object for pretty printing expressions */
class pp_fn {
    typedef scoped_map<expr, name, expr_hash, expr_eqp> aliases;
    typedef std::vector<std::pair<name, format>>        aliases_defs;
    frontend const & m_frontend;
    // State
    aliases          m_aliases;
    aliases_defs     m_aliases_defs;
    unsigned         m_num_steps;
    name             m_aux;
    // Configuration
    unsigned         m_indent;
    unsigned         m_max_depth;
    unsigned         m_max_steps;
    bool             m_implict;
    bool             m_notation;         //!< if true use notation
    bool             m_extra_lets;       //!< introduce extra let-expression to cope with sharing.
    unsigned         m_alias_min_weight; //!< minimal weight for creating an alias
    volatile bool    m_interrupted;


    // Create a scope for local definitions
    struct mk_scope {
        pp_fn &  m_fn;
        unsigned m_old_size;
        mk_scope(pp_fn & fn):m_fn(fn), m_old_size(fn.m_aliases_defs.size()) {
            m_fn.m_aliases.push();
        }
        ~mk_scope() {
            lean_assert(m_old_size <= m_fn.m_aliases_defs.size());
            m_fn.m_aliases.pop();
            m_fn.m_aliases_defs.resize(m_old_size);
        }
    };

    format nest(unsigned i, format const & f) { return ::lean::nest(i, f); }

    typedef std::pair<format, unsigned> result;

    /**
       \brief Return true iff \c e is an atomic operation.
    */
    bool is_atomic(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Value: case expr_kind::Type:
            return true;
        case expr_kind::App: case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Eq: case expr_kind::Let:
            return false;
        }
        return false;
    }

    result mk_result(format const & fmt, unsigned depth) {
        return mk_pair(fmt, depth);
    }

    result pp_ellipsis() {
        return mk_result(m_notation ? g_ellipsis_n_fmt : g_ellipsis_fmt, 1);
    }

    result pp_var(expr const & e) {
        unsigned vidx = var_idx(e);
        return mk_result(compose(format("#"), format(vidx)), 1);
    }

    result pp_constant(expr const & e) {
        return mk_result(::lean::pp(const_name(e)), 1);
    }

    result pp_value(expr const & e) {
        return mk_result(to_value(e).pp(m_notation), 1);
    }

    result pp_type(expr const & e) {
        if (e == Type()) {
            return mk_result(g_Type_fmt, 1);
        } else {
            return mk_result(format{g_Type_fmt, space(), ::lean::pp(ty_level(e))}, 1);
        }
    }

    /**
       \brief Return the operator associated with \c e.
       Return the null operator if there is none.

       We say \c e has an operator associated with it, if:

       1) \c e is associated with an operator.

       2) It is an application, and the function is associated with an
       operator.
    */
    operator_info get_operator(expr const & e) {
        operator_info op = m_frontend.find_op_for(e);
        if (op)
            return op;
        else if (is_app(e))
            return m_frontend.find_op_for(arg(e, 0));
        else
            return operator_info();
    }

    /**
       \brief Return the precedence of the given expression
    */
    unsigned get_operator_precedence(expr const & e) {
        if (is_constant(e)) {
            operator_info op = get_operator(e);
            return op ? op.get_precedence() : 0;
        } else if (is_eq(e)) {
            return g_eq_precedence;
        } else if (is_arrow(e)) {
            return g_arrow_precedence;
        } else {
            return 0;
        }
    }

    /** \brief Return true if the application \c e has the number of arguments expected by the operator \c op. */
    bool has_expected_num_args(expr const & e, operator_info const & op) {
        switch (op.get_fixity()) {
        case fixity::Infix: case fixity::Infixl: case fixity::Infixr:
            return num_args(e) == 3;
        case fixity::Prefix: case fixity::Postfix:
            return num_args(e) == 2;
        case fixity::Mixfixl: case fixity::Mixfixr:
            return num_args(e) == length(op.get_op_name_parts()) + 1;
        case fixity::Mixfixc:
            return num_args(e) == length(op.get_op_name_parts());
        }
        lean_unreachable();
        return false;
    }

    /**
       \brief Pretty print given expression and put parenthesis around
       it IF the pp of the expression is not a simple name.
    */
    result pp_child_with_paren(expr const & e, unsigned depth) {
        result r = pp(e, depth + 1);
        if (is_name(r.first)) {
            // We do not add a parenthis if the format object is just
            // a name. This can happen when \c e is a complicated
            // expression, but an alias is created for it.
            return r;
        } else {
            return mk_result(format{lp(), nest(1, format{r.first, rp()})}, r.second);
        }
    }

    /**
       \brief Pretty print given expression and put parenthesis around
       it if it is not atomic.
    */
    result pp_child(expr const & e, unsigned depth) {
        if (is_atomic(e))
            return pp(e, depth + 1);
        else
            return pp_child_with_paren(e, depth);
    }

    /**
        \brief Pretty print the child of an infix, prefix, postfix or
        mixfix operator. It will add parethesis when needed.
    */
    result pp_mixfix_child(operator_info const & op, expr const & e, unsigned depth) {
        if (is_atomic(e)) {
            return pp(e, depth + 1);
        } else {
            if (op.get_precedence() < get_operator_precedence(e))
                return pp(e, depth + 1);
            else
                return pp_child_with_paren(e, depth);
        }
    }

    /**
        \brief Pretty print the child of an associative infix
        operator. It will add parethesis when needed.
    */
    result pp_infix_child(operator_info const & op, expr const & e, unsigned depth) {
        if (is_atomic(e)) {
            return pp(e, depth + 1);
        } else {
            if (op.get_precedence() < get_operator_precedence(e) || op == get_operator(e))
                return pp(e, depth + 1);
            else
                return pp_child_with_paren(e, depth);
        }
    }

    result mk_infix(operator_info const & op, result const & lhs, result const & rhs) {
        unsigned r_weight = lhs.second + rhs.second + 1;
        format   r_format = group(format{lhs.first, space(), format(op.get_op_name()), line(), rhs.first});
        return mk_result(r_format, r_weight);
    }

    bool is_forall_expr(expr const & e) {
        return is_app(e) && arg(e, 0) == mk_forall_fn() && num_args(e) == 3;
    }

    bool is_exists_expr(expr const & e) {
        return is_app(e) && arg(e, 0) == mk_exists_fn() && num_args(e) == 3;
    }

    bool is_quant_expr(expr const & e, bool is_forall) {
        return is_forall ? is_forall_expr(e) : is_exists_expr(e);
    }

    /**
       \brief Collect nested quantifiers, and instantiate
       variables with unused names. Store in \c r the selected names
       and associated domains. Return the body of the sequence of
       nested quantifiers.
    */
    expr collect_nested_quantifiers(expr const & e, bool is_forall, buffer<std::pair<name, expr>> & r) {
        lean_assert(is_quant_expr(e, is_forall));
        if (is_lambda(arg(e, 2))) {
            expr lambda = arg(e, 2);
            name n1 = get_unused_name(lambda);
            r.push_back(mk_pair(n1, abst_domain(lambda)));
            expr b  = instantiate_with_closed(abst_body(lambda), mk_constant(n1));
            if (is_quant_expr(b, is_forall))
                return collect_nested_quantifiers(b, is_forall, r);
            else
                return b;
        } else {
            // Quantifier is not in normal form. That is, it might be
            //   (forall t p)  or (exists t p)  where p is not a lambda
            //   abstraction
            // So, we put it in normal form
            //   (forall t (fun x : t, p x))
            //   or
            //   (exists t (fun x : t, p x))
            expr new_body = mk_lambda("x", arg(e, 1), mk_app(lift_free_vars(arg(e, 2), 1), mk_var(0)));
            expr normal_form = mk_app(arg(e, 0), arg(e, 1), new_body);
            return collect_nested_quantifiers(normal_form, is_forall, r);
        }
    }

    result pp_quantifier(expr const & e, unsigned depth, bool is_forall) {
        buffer<std::pair<name, expr>> nested;
        expr b = collect_nested_quantifiers(e, is_forall, nested);
        format head;
        if (m_notation)
            head = is_forall ? g_forall_n_fmt : g_exists_n_fmt;
        else
            head = is_forall ? g_forall_fmt : g_exists_fmt;
        format sep  = comma();
        expr domain0 = nested[0].second;
        // TODO: the following code is very similar to pp_abstraction
        if (std::all_of(nested.begin() + 1, nested.end(), [&](std::pair<name, expr> const & p) { return p.second == domain0; })) {
            // Domain of all binders is the same
            format names    = pp_bnames(nested.begin(), nested.end(), false);
            result p_domain = pp_scoped_child(domain0, depth);
            result p_body   = pp_scoped_child(b, depth);
            format sig      = format{names, space(), colon(), space(), p_domain.first};
            format r_format = group(nest(m_indent, format{head, space(), sig, sep, line(), p_body.first}));
            return mk_result(r_format, p_domain.second + p_body.second + 1);
        } else {
            auto it  = nested.begin();
            auto end = nested.end();
            unsigned r_weight = 1;
            // PP binders in blocks (names ... : type)
            bool first = true;
            format bindings;
            while (it != end) {
                auto it2 = it;
                ++it2;
                while (it2 != end && it2->second == it->second) {
                    ++it2;
                }
                result p_domain = pp_scoped_child(it->second, depth);
                r_weight += p_domain.second;
                format block = group(nest(m_indent, format{lp(), pp_bnames(it, it2, true), space(), colon(), space(), p_domain.first, rp()}));
                if (first) {
                    bindings = block;
                    first = false;
                } else {
                    bindings += compose(line(), block);
                }
                it = it2;
            }
            result p_body   = pp_scoped_child(b, depth);
            format r_format = group(nest(m_indent, format{head, space(), group(bindings), sep, line(), p_body.first}));
            return mk_result(r_format, r_weight + p_body.second);
        }
    }

    result pp_forall(expr const & e, unsigned depth) {
        return pp_quantifier(e, depth, true);
    }

    result pp_exists(expr const & e, unsigned depth) {
        return pp_quantifier(e, depth, false);
    }

    /**
       \brief Pretty print an application.
    */
    result pp_app(expr const & e, unsigned depth) {
        operator_info op;
        if (m_notation && (op = get_operator(e)) && has_expected_num_args(e, op)) {
            result   p_arg;
            format   r_format;
            unsigned sz;
            unsigned r_weight = 1;
            switch (op.get_fixity()) {
            case fixity::Infix:
                return mk_infix(op, pp_mixfix_child(op, arg(e, 1), depth), pp_mixfix_child(op, arg(e, 2), depth));
            case fixity::Infixr:
                return mk_infix(op, pp_mixfix_child(op, arg(e, 1), depth), pp_infix_child(op, arg(e, 2), depth));
            case fixity::Infixl:
                return mk_infix(op, pp_infix_child(op, arg(e, 1), depth),  pp_mixfix_child(op, arg(e, 2), depth));
            case fixity::Prefix:
                p_arg = pp_infix_child(op, arg(e, 1), depth);
                sz  = op.get_op_name().size();
                return mk_result(group(format{format(op.get_op_name()), nest(sz+1, format{line(), p_arg.first})}),
                                 p_arg.second + 1);
            case fixity::Postfix:
                p_arg = pp_mixfix_child(op, arg(e, 1), depth);
                return mk_result(group(format{p_arg.first, space(), format(op.get_op_name())}),
                                 p_arg.second + 1);
            case fixity::Mixfixr: {
                // _ ID ... _ ID
                list<name> parts = op.get_op_name_parts();
                auto it = parts.begin();
                for (unsigned i = 1; i < num_args(e); i++) {
                    result p_arg = pp_mixfix_child(op, arg(e, i), depth);
                    r_format += format{p_arg.first, space(), format(*it), line()};
                    r_weight += p_arg.second;
                    ++it;
                }
                return mk_result(group(r_format), r_weight);
            }
            case fixity::Mixfixl: case fixity::Mixfixc: {
                // ID _ ... _
                // ID _ ... _ ID
                list<name> parts = op.get_op_name_parts();
                auto it = parts.begin();
                for (unsigned i = 1; i < num_args(e); i++) {
                    result p_arg = pp_mixfix_child(op, arg(e, i), depth);
                    unsigned sz  = it->size();
                    if (i > 1) r_format += space();
                    r_format    += format{format(*it), nest(sz+1, format{line(), p_arg.first})};
                    r_weight    += p_arg.second;
                    ++it;
                }
                if (it != parts.end()) {
                    // it is Mixfixc
                    r_format += format{space(), format(*it)};
                }
                return mk_result(group(r_format), r_weight);
            }}
            lean_unreachable();
            return mk_result(format(), 0);
        } else if (m_notation && is_forall_expr(e)) {
            return pp_forall(e, depth);
        } else if (m_notation && is_exists_expr(e)) {
            return pp_exists(e, depth);
        } else {
            // standard function application
            result p    = pp_child(arg(e, 0), depth);
            bool simple = is_constant(arg(e, 0)) && const_name(arg(e, 0)).size() <= m_indent + 4;
            unsigned indent = simple ? const_name(arg(e, 0)).size()+1 : m_indent;
            format   r_format = p.first;
            unsigned r_weight = p.second;
            for (unsigned i = 1; i < num_args(e); i++) {
                result p_arg = pp_child(arg(e, i), depth);
                r_format += format{i == 1 && simple ? space() : line(), p_arg.first};
                r_weight += p_arg.second;
            }
            return mk_result(group(nest(indent, r_format)), r_weight);
        }
    }

    /**
       \brief Collect nested Lambdas (or Pis), and instantiate
       variables with unused names. Store in \c r the selected names
       and associated domains. Return the body of the sequence of
       Lambda (of Pis).

       \remark The argument B is only relevant when processing
       condensed definitions. \see pp_abstraction_core.
    */
    std::pair<expr, expr> collect_nested(expr const & e, expr T, expr_kind k, buffer<std::pair<name, expr>> & r) {
        if (e.kind() == k && (!T || is_abstraction(T))) {
            name n1    = get_unused_name(e);
            r.push_back(mk_pair(n1, abst_domain(e)));
            expr b = instantiate_with_closed(abst_body(e), mk_constant(n1));
            if (T)
                T = instantiate_with_closed(abst_body(T), mk_constant(n1));
            return collect_nested(b, T, k, r);
        } else {
            return mk_pair(e, T);
        }
    }

    result pp_scoped_child(expr const & e, unsigned depth) {
        if (is_atomic(e)) {
            return pp(e, depth + 1, true);
        } else {
            mk_scope s(*this);
            result r = pp(e, depth + 1, true);
            if (m_aliases_defs.size() == s.m_old_size) {
                return r;
            } else {
                format r_format   = g_let_fmt;
                unsigned r_weight = 2;
                unsigned begin    = s.m_old_size;
                unsigned end      = m_aliases_defs.size();
                for (unsigned i = begin; i < end; i++) {
                    auto b = m_aliases_defs[i];
                    name const & n = b.first;
                    format beg = i == begin ? space() : line();
                    format sep = i < end - 1 ? comma() : format();
                    r_format += nest(3 + 1, format{beg, format(n), space(), g_assign_fmt, nest(n.size() + 1 + 2 + 1, format{space(), b.second, sep})});
                    // we do not store the alias definitin real weight. We know it is at least m_alias_min_weight
                    r_weight += m_alias_min_weight + 1;
                }
                r_format += format{line(), g_in_fmt, space(), nest(2 + 1, r.first)};
                r_weight += r.second;
                return mk_pair(group(r_format), r_weight);
            }
        }
    }

    result pp_arrow_body(expr const & e, unsigned depth) {
        if (is_atomic(e) || is_arrow(e)) {
            return pp(e, depth + 1);
        } else {
            return pp_child_with_paren(e, depth);
        }
    }

    template<typename It>
    format pp_bnames(It const & begin, It const & end, bool use_line) {
        auto it = begin;
        format r = format(it->first);
        ++it;
        for (; it != end; ++it) {
            r += compose(use_line ? line() : space(), format(it->first));
        }
        return r;
    }

    /**
       \brief Pretty print Lambdas, Pis and compact definitions.
       When T != 0, it is a compact definition.
       A compact definition is of the form

       Defintion Name Pi(x : A), B := Lambda (x : A), C

       it is printed as

       Defintion Name (x : A) : B := C

       This method only generates the
          (x : A) : B := C
       for compact definitions.

       \remark if T != 0, then T is Pi(x : A), B
    */
    result pp_abstraction_core(expr const & e, unsigned depth, expr T) {
        if (is_arrow(e)) {
            lean_assert(!T);
            result p_lhs    = pp_child(abst_domain(e), depth);
            result p_rhs    = pp_arrow_body(abst_body(e), depth);
            format r_format = group(format{p_lhs.first, space(), m_notation ? g_arrow_n_fmt : g_arrow_fmt, line(), p_rhs.first});
            return mk_result(r_format, p_lhs.second + p_rhs.second + 1);
        } else {
            buffer<std::pair<name, expr>> nested;
            auto p = collect_nested(e, T, e.kind(), nested);
            expr b = p.first;
            T = p.second;
            unsigned head_indent = m_indent;
            format head;
            if (!T) {
                if (m_notation) {
                    head = is_lambda(e) ? g_lambda_n_fmt : g_Pi_n_fmt;
                    head_indent = 2;
                } else {
                    head = is_lambda(e) ? g_lambda_fmt : g_Pi_fmt;
                    head_indent = is_lambda(e) ? 4 : 3;
                }
            }
            format body_sep;
            if (T) {
                format T_f = pp(T, 0).first;
                body_sep = format{space(), colon(), space(), T_f, space(), g_assign_fmt};
            } else {
                body_sep = comma();
            }
            expr domain0 = nested[0].second;
            if (std::all_of(nested.begin() + 1, nested.end(), [&](std::pair<name, expr> const & p) { return p.second == domain0; })) {
                // Domain of all binders is the same
                format names    = pp_bnames(nested.begin(), nested.end(), false);
                result p_domain = pp_scoped_child(domain0, depth);
                result p_body   = pp_scoped_child(b, depth);
                format sig      = format{names, space(), colon(), space(), p_domain.first};
                if (T)
                    sig = format{lp(), sig, rp()};
                format r_format = group(nest(head_indent, format{head, space(), sig, body_sep, line(), p_body.first}));
                return mk_result(r_format, p_domain.second + p_body.second + 1);
            } else {
                auto it  = nested.begin();
                auto end = nested.end();
                unsigned r_weight = 1;
                // PP binders in blocks (names ... : type)
                bool first = true;
                format bindings;
                while (it != end) {
                    auto it2 = it;
                    ++it2;
                    while (it2 != end && it2->second == it->second) {
                        ++it2;
                    }
                    result p_domain = pp_scoped_child(it->second, depth);
                    r_weight += p_domain.second;
                    format block = group(nest(m_indent, format{lp(), pp_bnames(it, it2, true), space(), colon(), space(), p_domain.first, rp()}));
                    if (first) {
                        bindings = block;
                        first = false;
                    } else {
                        bindings += compose(line(), block);
                    }
                    it = it2;
                }
                result p_body   = pp_scoped_child(b, depth);
                format r_format = group(nest(head_indent, format{head, space(), group(bindings), body_sep, line(), p_body.first}));
                return mk_result(r_format, r_weight + p_body.second);
            }
        }
    }

    result pp_abstraction(expr const & e, unsigned depth) {
        return pp_abstraction_core(e, depth, expr());
    }

    expr collect_nested_let(expr const & e, buffer<std::pair<name, expr>> & bindings) {
        if (is_let(e)) {
            name n1    = get_unused_name(e);
            bindings.push_back(mk_pair(n1, let_value(e)));
            expr b = instantiate_with_closed(let_body(e), mk_constant(n1));
            return collect_nested_let(b, bindings);
        } else {
            return e;
        }
    }

    result pp_let(expr const & e, unsigned depth) {
        buffer<std::pair<name, expr>> bindings;
        expr body = collect_nested_let(e, bindings);
        unsigned r_weight = 2;
        format r_format = g_let_fmt;
        unsigned sz = bindings.size();
        for (unsigned i = 0; i < sz; i++) {
            auto b = bindings[i];
            name const & n = b.first;
            result p_def = pp(b.second, depth+1);
            format beg = i == 0 ? space() : line();
            format sep = i < sz - 1 ? comma() : format();
            r_format += nest(3 + 1, format{beg, format(n), space(), g_assign_fmt, nest(n.size() + 1 + 2 + 1, format{space(), p_def.first, sep})});
            r_weight += p_def.second;
        }
        result p_body = pp(body, depth+1);
        r_weight += p_body.second;
        r_format += format{line(), g_in_fmt, space(), nest(2 + 1, p_body.first)};
        return mk_pair(group(r_format), r_weight);
    }

    /** \brief Pretty print the child of an equality. */
    result pp_eq_child(expr const & e, unsigned depth) {
        if (is_atomic(e)) {
            return pp(e, depth + 1);
        } else {
            if (g_eq_precedence < get_operator_precedence(e))
                return pp(e, depth + 1);
            else
                return pp_child_with_paren(e, depth);
        }
    }

    /** \brief Pretty print an equality */
    result pp_eq(expr const & e, unsigned depth) {
        result p_arg1, p_arg2;
        format r_format;
        p_arg1 = pp_eq_child(eq_lhs(e), depth);
        p_arg2 = pp_eq_child(eq_rhs(e), depth);
        r_format = group(format{p_arg1.first, space(), g_eq_fmt, line(), p_arg2.first});
        return mk_result(r_format, p_arg1.second + p_arg2.second + 1);
    }

    result pp(expr const & e, unsigned depth, bool main = false) {
        check_interrupted(m_interrupted);
        if (!is_atomic(e) && (m_num_steps > m_max_steps || depth > m_max_depth)) {
            return pp_ellipsis();
        } else {
            m_num_steps++;
            if (m_extra_lets && is_shared(e)) {
                auto it = m_aliases.find(e);
                if (it != m_aliases.end())
                    return mk_result(format(it->second), 1);
            }
            result r;
            switch (e.kind()) {
            case expr_kind::Var:        r = pp_var(e);                break;
            case expr_kind::Constant:   r = pp_constant(e);           break;
            case expr_kind::Value:      r = pp_value(e);              break;
            case expr_kind::App:        r = pp_app(e, depth);         break;
            case expr_kind::Lambda:
            case expr_kind::Pi:         r = pp_abstraction(e, depth); break;
            case expr_kind::Type:       r = pp_type(e);               break;
            case expr_kind::Eq:         r = pp_eq(e, depth);          break;
            case expr_kind::Let:        r = pp_let(e, depth);         break;
            }
            if (!main && m_extra_lets && is_shared(e) && r.second > m_alias_min_weight) {
                name new_aux = name(m_aux, m_aliases_defs.size()+1);
                m_aliases.insert(e, new_aux);
                m_aliases_defs.push_back(mk_pair(new_aux, r.first));
                return mk_result(format(new_aux), 1);
            }
            return r;
        }
    }

    void set_options(options const & opts) {
        m_indent           = get_pp_indent(opts);
        m_max_depth        = get_pp_max_depth(opts);
        m_max_steps        = get_pp_max_steps(opts);
        m_implict          = get_pp_implicit(opts);
        m_notation         = get_pp_notation(opts);
        m_extra_lets       = get_pp_extra_lets(opts);
        m_alias_min_weight = get_pp_alias_min_weight(opts);
    }


    struct found_prefix {};
    bool uses_prefix(expr const & e, name const & prefix) {
        auto f = [&](expr const & e, unsigned offset) {
            if (is_constant(e)) {
                if (is_prefix_of(prefix, const_name(e))) throw found_prefix();
            } else if (is_abstraction(e)) {
                if (is_prefix_of(prefix, abst_name(e))) throw found_prefix();
            } else if (is_let(e)) {
                if (is_prefix_of(prefix, let_name(e))) throw found_prefix();
            }
        };
        try {
            for_each_fn<decltype(f)> visitor(f);
            visitor(e);
            return false;
        } catch (found_prefix) {
            return true;
        }
    }

    name find_unused_prefix(expr const & e) {
        if (!uses_prefix(e, g_kappa))
            return g_kappa;
        else if (!uses_prefix(e, g_pho))
            return g_pho;
        else {
            unsigned i = 1;
            name n(g_nu, i);
            while (uses_prefix(e, n)) {
                i++;
                n = name(g_nu, i);
            }
            return n;
        }
    }

    void init(expr const & e) {
        m_aliases.clear();
        m_aliases_defs.clear();
        m_num_steps = 0;
        m_aux = find_unused_prefix(e);
    }

public:
    pp_fn(frontend const & fe, options const & opts):
        m_frontend(fe) {
        set_options(opts);
        m_interrupted = false;
    }

    format operator()(expr const & e) {
        init(e);
        return pp_scoped_child(e, 0).first;
    }

    format pp_definition(expr const & v, expr const & t) {
        init(mk_app(v, t));
        expr T(t);
        return pp_abstraction_core(v, 0, T).first;
    }

    void set_interrupt(bool flag) {
        m_interrupted = flag;
    }
};

class pp_formatter_cell : public formatter_cell {
    frontend const &         m_frontend;
    interruptable_ptr<pp_fn> m_pp_fn;
    volatile bool            m_interrupted;

    format pp(expr const & e, options const & opts) {
        pp_fn fn(m_frontend, opts);
        scoped_set_interruptable_ptr<pp_fn> set(m_pp_fn, &fn);
        return fn(e);
    }

    format pp(context const & c, expr const & e, bool include_e, options const & opts) {
        unsigned indent = get_pp_indent(opts);
        format r;
        bool first = true;
        expr c2   = context_to_lambda(c, e);
        while (is_fake_context(c2)) {
            check_interrupted(m_interrupted);
            name n1 = get_unused_name(c2);
            format entry = format{format(n1), space(), colon(), space(), pp(fake_context_domain(c2), opts)};
            expr val = fake_context_value(c2);
            if (val)
                entry += format{space(), g_assign_fmt, nest(indent, format{line(), pp(val, opts)})};
            if (first) {
                r = group(entry);
                first = false;
            } else {
                r += format{line(), group(entry)};
            }
            c2 = instantiate_with_closed(fake_context_rest(c2), mk_constant(n1));
        }
        if (include_e) {
            if (first)
                r += format{line(), pp(c2, opts)};
            else
                r = pp(c2, opts);
        } else {
            return r;
        }
        return r;
    }

    format pp_definition(char const * kwd, name const & n, expr const & t, expr const & v, options const & opts) {
        unsigned indent = get_pp_indent(opts);
        format def = format{highlight_command(format(kwd)), space(), format(n), space(), colon(), space(),
                            pp(t, opts), space(), g_assign_fmt, line(), pp(v, opts)};
        return group(nest(indent, def));
    }

    format pp_compact_definition(char const * kwd, name const & n, expr const & t, expr const & v, options const & opts) {
        expr it1 = t;
        expr it2 = v;
        while (is_pi(it1) && is_lambda(it2)) {
            check_interrupted(m_interrupted);
            if (abst_domain(it1) != abst_domain(it2))
                return pp_definition(kwd, n, t, v, opts);
            it1 = abst_body(it1);
            it2 = abst_body(it2);
        }
        if (!is_lambda(v) || is_pi(it1)) {
            return pp_definition(kwd, n, t, v, opts);
        } else {
            lean_assert(is_lambda(v));
            pp_fn fn(m_frontend, opts);
            scoped_set_interruptable_ptr<pp_fn> set(m_pp_fn, &fn);
            format def = fn.pp_definition(v, t);
            return format{highlight_command(format(kwd)), space(), format(n), def};
        }
    }

    format pp_uvar_decl(object const & obj, options const & opts) {
        return format{highlight_command(format(obj.keyword())), space(), format(obj.get_name()), space(), format("\u2265"), space(), ::lean::pp(obj.get_cnstr_level())};
    }

    format pp_postulate(object const & obj, options const & opts) {
        return format{highlight_command(format(obj.keyword())), space(), format(obj.get_name()), space(), colon(), space(), pp(obj.get_type(), opts)};
    }

    format pp_definition(object const & obj, options const & opts) {
        return pp_compact_definition(obj.keyword(), obj.get_name(), obj.get_type(), obj.get_value(), opts);
    }

    format pp_notation_decl(object const & obj, options const & opts) {
        notation_declaration const & n = *(static_cast<notation_declaration const *>(obj.cell()));
        return format{::lean::pp(n.get_op()), space(), colon(), space(), pp(n.get_expr(), opts)};
    }

public:
    pp_formatter_cell(frontend const & fe):
        m_frontend(fe) {
        m_interrupted = false;
    }

    virtual ~pp_formatter_cell() {
    }

    virtual format operator()(expr const & e, options const & opts) {
        return pp(e, opts);
    }

    virtual format operator()(context const & c, options const & opts) {
        return pp(c, Type(), false, opts);
    }

    virtual format operator()(context const & c, expr const & e, bool format_ctx, options const & opts) {
        if (format_ctx) {
            return pp(c, e, true, opts);
        } else {
            expr c2   = context_to_lambda(c, e);
            while (is_fake_context(c2)) {
                check_interrupted(m_interrupted);
                expr const & rest = fake_context_rest(c2);
                name n1 = get_unused_name(rest);
                c2 = instantiate_with_closed(rest, mk_constant(n1));
            }
            return pp(c2, opts);
        }
    }

    virtual format operator()(object const & obj, options const & opts) {
        switch (obj.kind()) {
        case object_kind::UVarDeclaration:  return pp_uvar_decl(obj, opts);
        case object_kind::Postulate:        return pp_postulate(obj, opts);
        case object_kind::Definition:       return pp_definition(obj, opts);
        case object_kind::Neutral:
            if (dynamic_cast<notation_declaration const *>(obj.cell())) {
                // If the object is not notation, then the object was
                // created in different frontend, and we ignore it.
                return pp_notation_decl(obj, opts);
            } else {
                return format("Unknown neutral object");
            }
        }
        lean_unreachable();
        return format();
    }

    virtual format operator()(environment const & env, options const & opts) {
        format r;
        bool first = true;
        std::for_each(env.begin_objects(),
                      env.end_objects(),
                      [&](object const & obj) {
                          check_interrupted(m_interrupted);
                          if (first) first = false; else r += line();
                          r += operator()(obj, opts);
                      });
        return r;
    }

    virtual void set_interrupt(bool flag) {
        m_pp_fn.set_interrupt(flag);
        m_interrupted = flag;
    }
};

formatter mk_pp_formatter(frontend const & fe) {
    return formatter(new pp_formatter_cell(fe));
}

std::ostream & operator<<(std::ostream & out, frontend const & fe) {
    options const & opts = fe.get_state().get_options();
    formatter fmt = mk_pp_formatter(fe);
    out << mk_pair(fmt(fe, opts), opts);
    return out;
}
}

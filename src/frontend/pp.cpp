/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <memory>
#include "pp.h"
#include "frontend.h"
#include "context.h"
#include "scoped_map.h"
#include "occurs.h"
#include "instantiate.h"
#include "builtin_notation.h"
#include "context_to_lambda.h"
#include "printer.h"
#include "options.h"

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

#ifndef LEAN_DEFAULT_PP_ALIAS_MIN_DEPTH
#define LEAN_DEFAULT_PP_ALIAS_MIN_DEPTH 1000 //TODO: fix to reasonable value
#endif

namespace lean {
static format g_Type_fmt      = highlight_builtin(format("Type"));
static format g_eq_fmt        = format("=");
static char const * g_eq_sym  = "eq";
static unsigned g_eq_sz       = strlen(g_eq_sym);
static format g_eq_sym_fmt    = format(g_eq_sym);
static format g_lambda_fmt    = highlight_keyword(format("\u03BB"));
static format g_Pi_fmt        = highlight_keyword(format("\u03A0"));
static format g_arrow_fmt     = highlight_keyword(format("\u2192"));
static format g_ellipsis_fmt  = highlight(format("\u2026"));
static format g_let_fmt       = highlight_keyword(format("let"));
static format g_in_fmt        = highlight_keyword(format("in"));
static format g_assign_fmt    = highlight_keyword(format(":="));
static format g_geq_fmt       = format("\u2265");

static name g_pp_max_depth       {"pp", "max_depth"};
static name g_pp_max_steps       {"pp", "max_steps"};
static name g_pp_implicit        {"pp", "implicit"};
static name g_pp_notation        {"pp", "notation"};
static name g_pp_extra_lets      {"pp", "extra_lets"};
static name g_pp_alias_min_depth {"pp", "alias_min_depth"};

unsigned get_pp_max_depth(options const & opts)       { return opts.get_unsigned(g_pp_max_depth, LEAN_DEFAULT_PP_MAX_DEPTH); }
unsigned get_pp_max_steps(options const & opts)       { return opts.get_unsigned(g_pp_max_steps, LEAN_DEFAULT_PP_MAX_STEPS); }
bool     get_pp_implicit(options const & opts)        { return opts.get_bool(g_pp_implicit, LEAN_DEFAULT_PP_IMPLICIT); }
bool     get_pp_notation(options const & opts)        { return opts.get_bool(g_pp_notation, LEAN_DEFAULT_PP_NOTATION); }
bool     get_pp_extra_lets(options const & opts)      { return opts.get_bool(g_pp_extra_lets, LEAN_DEFAULT_PP_EXTRA_LETS); }
unsigned get_pp_alias_min_depth(options const & opts) { return opts.get_unsigned(g_pp_alias_min_depth, LEAN_DEFAULT_PP_ALIAS_MIN_DEPTH); }

/**
   \brief Return a fresh name for the given abstraction.
   By fresh, we mean a name that is not used for any constant in abst_body(e).
   The resultant name is based on abst_name(e).
*/
name get_unused_name(expr const & e) {
    name const & n = abst_name(e);
    name n1    = n;
    unsigned i = 1;
    while (occurs(n1, abst_body(e))) {
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
    bool             m_notation;        //!< if true use notation
    bool             m_extra_lets;      //!< introduce extra let-expression to cope with sharing.
    unsigned         m_alias_min_depth; //!< minimal depth to create an alias

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
        return mk_result(g_ellipsis_fmt, 1);
    }

    result pp_var(expr const & e) {
        unsigned vidx = var_idx(e);
        return mk_result(compose(format("#"), format(vidx)), 1);
    }

    result pp_constant(expr const & e) {
        return mk_result(::lean::pp(const_name(e)), 1);
    }

    result pp_value(expr const & e) {
        return mk_result(to_value(e).pp(), 1);
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
       Return the nil operator if there is none.

       We say \c e has an operator associated with it, if:

       1) It is a constant and there is an operator associated with it.

       2) It is an application, and the function is a constant \c c with an
       operator associated with \c c.
    */
    operator_info get_operator(expr const & e) {
        if (is_constant(e))
            return m_frontend.find_op_for(const_name(e));
        else if (is_app(e) && is_constant(arg(e, 0)))
            return m_frontend.find_op_for(const_name(arg(e, 0)));
        else
            return operator_info();
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
       \brief Pretty print given expression and put parenthesis around it.
    */
    result pp_child_with_paren(expr const & e, unsigned depth) {
        result r = pp(e, depth + 1);
        return mk_result(format{lp(), r.first, rp()}, r.second);
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
            operator_info op_child = get_operator(e);
            if (op_child && op.get_precedence() < op_child.get_precedence())
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
            operator_info op_child = get_operator(e);
            if (op_child && (op == op_child || op.get_precedence() < op_child.get_precedence()))
                return pp(e, depth + 1);
            else
                return pp_child_with_paren(e, depth);
        }
    }

    result mk_infix(operator_info const & op, result const & lhs, result const & rhs) {
        unsigned r_depth  = std::max(lhs.second, rhs.second) + 1;
        format   r_format = group(format{lhs.first, space(), format(op.get_op_name()), line(), rhs.first});
        return mk_result(r_format, r_depth);
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
            unsigned r_depth = 0;
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
                    r_depth   = std::max(r_depth, p_arg.second);
                    ++it;
                }
                return mk_result(group(r_format), r_depth + 1);
            }
            case fixity::Mixfixl: case fixity::Mixfixc: {
                // ID _ ... _
                // ID _ ... _ ID
                list<name> parts = op.get_op_name_parts();
                auto it = parts.begin();
                for (unsigned i = 1; i < num_args(e); i++) {
                    result p_arg = pp_mixfix_child(op, arg(e, i), depth);
                    unsigned sz  = it->size();
                    r_format    += format{format(*it), nest(sz+1, format{line(), p_arg.first})};
                    r_depth      = std::max(r_depth, p_arg.second);
                    ++it;
                }
                if (it != parts.end()) {
                    // it is Mixfixc
                    r_format += format{space(), format(*it)};
                }
                return mk_result(group(r_format), r_depth + 1);
            }}
            lean_unreachable();
            return mk_result(format(), 0);
        } else {
            // standard function application
            result p = pp_child(arg(e, 0), depth);
            format   r_format = p.first;
            unsigned r_depth  = p.second;
            for (unsigned i = 1; i < num_args(e); i++) {
                result p_arg = pp_child(arg(e, i), depth);
                r_format += format{line(), p_arg.first};
                r_depth   = std::max(r_depth, p_arg.second);
            }
            return mk_result(group(nest(m_indent, r_format)), r_depth + 1);
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
        if (e.kind() == k) {
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
            return pp(e, depth + 1);
        } else {
            mk_scope s(*this);
            // TODO: create Let with new aliases
            return pp(e, depth+1);
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
            format r_format = group(format{p_lhs.first, space(), g_arrow_fmt, line(), p_rhs.first});
            return mk_result(r_format, std::max(p_lhs.second, p_rhs.second) + 1);
        } else {
            buffer<std::pair<name, expr>> nested;
            auto p = collect_nested(e, T, e.kind(), nested);
            expr b = p.first;
            T = p.second;
            lean_assert(b.kind() != e.kind());
            format head;
            if (!T) {
                head = is_lambda(e) ? g_lambda_fmt : g_Pi_fmt;
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
                format r_format = group(nest(m_indent, format{head, space(), sig, body_sep, line(), p_body.first}));
                return mk_result(r_format, std::max(p_domain.second, p_body.second)+1);
            } else {
                auto it  = nested.begin();
                auto end = nested.end();
                unsigned r_depth = 0;
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
                    r_depth = std::max(r_depth, p_domain.second);
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
                format r_format = group(nest(m_indent, format{head, space(), group(bindings), body_sep, line(), p_body.first}));
                return mk_result(r_format, std::max(r_depth, p_body.second)+1);
            }
        }
    }

    result pp_abstraction(expr const & e, unsigned depth) {
        return pp_abstraction_core(e, depth, expr());
    }

    result pp_let(expr const & e, unsigned depth) {
        // TODO
        return mk_result(format("TODO"), 1);
    }

    /** \brief Pretty print the child of an equality. */
    result pp_eq_child(expr const & e, unsigned depth) {
        if (is_atomic(e)) {
            return pp(e, depth + 1);
        } else {
            operator_info op_child = get_operator(e);
            if (op_child && g_eq_precedence < op_child.get_precedence())
                return pp(e, depth + 1);
            else
                return pp_child_with_paren(e, depth);
        }
    }

    /** \brief Pretty print an equality */
    result pp_eq(expr const & e, unsigned depth) {
        result p_arg1, p_arg2;
        format r_format;
        if (m_notation) {
            p_arg1 = pp_eq_child(eq_lhs(e), depth);
            p_arg2 = pp_eq_child(eq_rhs(e), depth);
            r_format = group(format{p_arg1.first, space(), g_eq_fmt, line(), p_arg2.first});

        } else {
            p_arg1 = pp_child(eq_lhs(e), depth);
            p_arg2 = pp_child(eq_rhs(e), depth);
            r_format = group(format{g_eq_sym_fmt, nest(g_eq_sz + 1,
                                                       format{line(), p_arg1.first,
                                                              line(), p_arg2.first})});
        }
        return mk_result(r_format, std::max(p_arg1.second, p_arg2.second) + 1);
    }

    result pp(expr const & e, unsigned depth) {
        if (m_num_steps > m_max_steps || depth > m_max_depth) {
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
            if (m_extra_lets && is_shared(e) && r.second > m_alias_min_depth) {
                lean_unreachable(); // TODO: remove
                std::cout << "DEPTH: " << r.second << "\n";
                name new_aux = name(m_aux, m_aliases.size());
                m_aliases.insert(e, new_aux);
                return mk_result(format(new_aux), 1);
            }
            return r;
        }
    }

    void set_options(options const & opts) {
        m_indent          = get_pp_indent(opts);
        m_max_depth       = get_pp_max_depth(opts);
        m_max_steps       = get_pp_max_steps(opts);
        m_implict         = get_pp_implicit(opts);
        m_notation        = get_pp_notation(opts);
        m_extra_lets      = get_pp_extra_lets(opts);
        m_alias_min_depth = get_pp_alias_min_depth(opts);
    }

    void init() {
        m_aliases.clear();
        m_aliases_defs.clear();
        m_num_steps = 0;
        m_aux = name("aux"); // TODO: find non used prefix
    }

public:
    pp_fn(frontend const & fe, options const & opts):
        m_frontend(fe) {
        set_options(opts);
    }

    format operator()(expr const & e) {
        init();
        return pp(e, 0).first;
    }

    format pp_definition(expr const & v, expr const & t) {
        init();
        expr T(t);
        return pp_abstraction_core(v, 0, T).first;
    }
};

class pp_formatter_cell : public formatter_cell {
    frontend const & m_frontend;
    options          m_options;
    unsigned         m_indent;

    format pp(expr const & e) {
        return pp_fn(m_frontend, m_options)(e);
    }

    format pp(context const & c, expr const & e, bool include_e) {
        format r;
        bool first = true;
        expr c2   = context_to_lambda(c, e);
        while (is_fake_context(c2)) {
            name n1 = get_unused_name(c2);
            format entry = format{format(n1), space(), colon(), space(), pp(fake_context_domain(c2))};
            expr val = fake_context_value(c2);
            if (val)
                entry += format{space(), g_assign_fmt, nest(m_indent, format{line(), pp(val)})};
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
                r += format{line(), pp(c2)};
            else
                r = pp(c2);
        } else {
            return r;
        }
        return r;
    }

    format pp_definition(char const * kwd, name const & n, expr const & t, expr const & v) {
        format def = format{highlight_command(format(kwd)), space(), format(n), space(), colon(), space(),
                            pp(t), space(), g_assign_fmt, line(), pp(v)};
        return group(nest(m_indent, def));
    }

    format pp_compact_definition(char const * kwd, name const & n, expr const & t, expr const & v) {
        expr it1 = t;
        expr it2 = v;
        while (is_pi(it1) && is_lambda(it2)) {
            if (abst_domain(it1) != abst_domain(it2))
                return pp_definition(kwd, n, t, v);
            it1 = abst_body(it1);
            it2 = abst_body(it2);
        }
        if (!is_lambda(v) || is_pi(it1) || is_lambda(it2)) {
            return pp_definition(kwd, n, t, v);
        } else {
            lean_assert(is_lambda(v));
            format def = pp_fn(m_frontend, m_options).pp_definition(v, t);
            return format{highlight_command(format(kwd)), space(), format(n), def};
        }
    }

    format pp_uvar_decl(object const & obj) {
        return format{highlight_command(format(obj.keyword())), space(), format(obj.get_name()), space(), format("\u2265"), space(), ::lean::pp(obj.get_cnstr_level())};
    }

    format pp_postulate(object const & obj) {
        return format{highlight_command(format(obj.keyword())), space(), format(obj.get_name()), space(), colon(), space(), pp(obj.get_type())};
    }

    format pp_definition(object const & obj) {
        return pp_compact_definition(obj.keyword(), obj.get_name(), obj.get_type(), obj.get_value());
    }

    format pp_notation_decl(object const & obj) {
        return ::lean::pp(*(static_cast<notation_declaration const *>(obj.cell())));
    }

public:
    pp_formatter_cell(frontend const & fe, options const & opts):
        m_frontend(fe),
        m_options(opts) {
        m_indent = get_pp_indent(opts);
    }

    virtual ~pp_formatter_cell() {
    }

    virtual format operator()(expr const & e) {
        return pp(e);
    }

    virtual format operator()(context const & c) {
        return pp(c, Type(), false);
    }

    virtual format operator()(context const & c, expr const & e, bool format_ctx) {
        if (format_ctx) {
            return pp(c, e, true);
        } else {
            expr c2   = context_to_lambda(c, e);
            while (is_fake_context(c2)) {
                expr const & rest = fake_context_rest(c2);
                name n1 = get_unused_name(rest);
                c2 = instantiate_with_closed(rest, mk_constant(n1));
            }
            return pp(c2);
        }
    }

    virtual format operator()(object const & obj) {
        switch (obj.kind()) {
        case object_kind::UVarDeclaration:  return pp_uvar_decl(obj);
        case object_kind::Postulate:        return pp_postulate(obj);
        case object_kind::Definition:       return pp_definition(obj);
        case object_kind::Neutral:
            if (dynamic_cast<notation_declaration const *>(obj.cell())) {
                // If the object is not notation, then the object was
                // created in different frontend, and we ignore it.
                return pp_notation_decl(obj);
            } else {
                return format("Unknown neutral object");
            }
        }
        lean_unreachable();
        return format();
    }

    virtual format operator()(environment const & env) {
        format r;
        bool first = true;
        std::for_each(env.begin_objects(),
                      env.end_objects(),
                      [&](object const & obj) {
                          if (first) first = false; else r += line();
                          r += operator()(obj);
                      });
        return r;
    }
};

formatter mk_pp_formatter(frontend const & fe, options const & opts) {
    return formatter(new pp_formatter_cell(fe, opts));
}

std::ostream & operator<<(std::ostream & out, frontend const & fe) {
    formatter fmt = mk_pp_formatter(fe, options());
    out << fmt(fe.get_environment());
    return out;
}
}

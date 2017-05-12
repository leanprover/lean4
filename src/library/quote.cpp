/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "library/placeholder.h"
#include "library/constants.h"
#include "library/annotation.h"
#include "library/kernel_serializer.h"
#include "library/exception.h"
#include "library/util.h"
#include "library/quote.h"
#include "library/type_context.h"

namespace lean {
static std::string * g_expr_quote_opcode  = nullptr;
static std::string * g_pexpr_quote_opcode = nullptr;
static expr * g_expr                = nullptr;
static expr * g_pexpr               = nullptr;
static name * g_expr_quote_macro    = nullptr;
static name * g_pexpr_quote_macro   = nullptr;

/** \brief The quoted expression macro is a compact way of encoding quoted expressions inside Lean expressions.
    It is used to represent values of types `reflected e` or `expr`. */
class expr_quote_macro : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_expr_quote_macro; }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        expr const & e = get_expr_quote_value(m);
        expr ty = ctx.check(e, infer_only);
        if (auto l = dec_level(get_level(ctx, ty))) {
            return mk_app(mk_constant(get_reflected_name(), {*l}), ty, e);
        } else {
            return *g_expr;
        }
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        return optional<expr>();
    }
    virtual unsigned trust_level() const { return 0; }
    virtual void display(std::ostream & out) const {
        out << "quote";
    }
    virtual format pp(formatter const &) const {
        return format("quote");
    }
    virtual bool is_atomic_pp(bool, bool) const { return false; }
    virtual void write(serializer & s) const { s << *g_expr_quote_opcode; }
};

/** \brief A compact way of encoding quoted pre-expressions inside Lean expressions. */
class pexpr_quote_macro : public macro_definition_cell {
    expr m_value;
public:
    pexpr_quote_macro(expr const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const {
        return m_value < static_cast<pexpr_quote_macro const &>(d).m_value;
    }
    virtual name get_name() const { return *g_pexpr_quote_macro; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const {
        return *g_pexpr;
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        return optional<expr>();
    }
    virtual unsigned trust_level() const { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const {
        /* Hack: we do *not* compare m_value's because quoted expressions may contain
           relevant position information that is ignored by the equality predicate for expressions.
        */
        return this == &other;
    }
    char const * prefix() const {
        return "``(";
    }
    virtual void display(std::ostream & out) const {
        out << "``(" << m_value << ")";
    }
    virtual format pp(formatter const & fmt) const {
        return format("``(") + nest(2, fmt(m_value)) + format(")");
    }
    virtual bool is_atomic_pp(bool, bool) const { return false; }
    virtual unsigned hash() const { return m_value.hash(); }
    virtual void write(serializer & s) const { s << *g_pexpr_quote_opcode << m_value; }
    expr const & get_value() const { return m_value; }
};

expr mk_expr_quote(expr const & e) {
    return mk_macro(macro_definition(new expr_quote_macro()), 1, &e);
}
expr mk_pexpr_quote(expr const & e) {
    return mk_macro(macro_definition(new pexpr_quote_macro(e)));
}

bool is_expr_quote(expr const & e) {
    return is_macro(e) && dynamic_cast<expr_quote_macro const *>(macro_def(e).raw()) != nullptr;
}
bool is_pexpr_quote(expr const & e) {
    return is_macro(e) && dynamic_cast<pexpr_quote_macro const *>(macro_def(e).raw()) != nullptr;
}

expr const & get_expr_quote_value(expr const & e) {
    lean_assert(is_expr_quote(e));
    return macro_arg(e, 0);
}

expr const & get_pexpr_quote_value(expr const & e) {
    lean_assert(is_pexpr_quote(e));
    return static_cast<pexpr_quote_macro const *>(macro_def(e).raw())->get_value();
}

static name * g_antiquote = nullptr;

expr mk_antiquote(expr const & e) { return mk_annotation(*g_antiquote, e); }
bool is_antiquote(expr const & e) { return is_annotation(e, *g_antiquote); }
expr const & get_antiquote_expr(expr const & e) {
    lean_assert(is_antiquote(e));
    return get_annotation_arg(e);
}

expr mk_pexpr_quote_and_substs(expr const & e, bool is_strict) {
    name x("_x");
    buffer<expr> locals;
    buffer<expr> aqs;
    expr s = replace(e, [&](expr const & t, unsigned) {
            if (is_antiquote(t)) {
                expr local = mk_local(mk_fresh_name(), x.append_after(locals.size() + 1),
                                      mk_expr_placeholder(), binder_info());
                locals.push_back(local);
                aqs.push_back(get_antiquote_expr(t));
                return some_expr(local);
            }
            if (is_local(t) && is_strict) {
                throw generic_exception(t, "unexpected local in quotation expression");
            }
            return none_expr();
        });
    expr r        = mk_pexpr_quote(Fun(locals, s));
    expr subst    = mk_constant(get_expr_subst_name());
    expr to_pexpr = mk_constant(get_to_pexpr_name());
    for (expr const & aq : aqs) {
        r = mk_app(subst, r, mk_app(to_pexpr, aq));
    }
    return r;
}

void initialize_quote() {
    g_expr_quote_macro    = new name("expr_quote_macro");
    g_pexpr_quote_macro   = new name("pexpr_quote_macro");
    g_expr_quote_opcode   = new std::string("Quote");
    g_pexpr_quote_opcode  = new std::string("PQuote");
    g_expr           = new expr(mk_app(Const(get_expr_name()), mk_bool_tt()));
    g_pexpr          = new expr(mk_app(Const(get_expr_name()), mk_bool_ff()));

    g_antiquote  = new name("antiquote");
    register_annotation(*g_antiquote);

    register_macro_deserializer(*g_expr_quote_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_expr_quote(args[0]);
                                });
    register_macro_deserializer(*g_pexpr_quote_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    expr e;
                                    d >> e;
                                    return mk_pexpr_quote(e);
                                });
}

void finalize_quote() {
    delete g_expr_quote_macro;
    delete g_pexpr_quote_macro;
    delete g_expr_quote_opcode;
    delete g_pexpr_quote_opcode;
    delete g_expr;
    delete g_pexpr;
    delete g_antiquote;
}
}

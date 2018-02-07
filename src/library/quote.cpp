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
static expr * g_expr                = nullptr;
static expr * g_pexpr               = nullptr;
static name * g_expr_quote_pre      = nullptr;
static name * g_expr_quote_macro    = nullptr;

/** \brief A compact way of encoding quoted expressions inside Lean expressions. Used for values of type
    `reflected e` and `pexpr`. */
class expr_quote_macro : public macro_definition_cell {
    expr m_value;
    bool m_reflected;
public:
    expr_quote_macro(expr const & v, bool reflected):m_value(v), m_reflected(reflected) {}
    virtual bool lt(macro_definition_cell const & d) const override {
        return m_value < static_cast<expr_quote_macro const &>(d).m_value;
    }
    virtual name get_name() const override { return *g_expr_quote_macro; }
    virtual expr check_type(expr const &, abstract_type_context & ctx, bool infer_only) const override {
        if (m_reflected) {
            expr ty = ctx.check(m_value, infer_only);
            return mk_app(mk_constant(get_reflected_name(), {get_level(ctx, ty)}), ty, m_value);
        } else {
            return *g_pexpr;
        }
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override {
        return optional<expr>();
    }
    virtual unsigned trust_level() const override { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const override {
        /* Hack: we do *not* compare m_value's because quoted expressions may contain
           relevant position information that is ignored by the equality predicate for expressions.
        */
        return this == &other;
    }
    char const * prefix() const {
        return m_reflected ? "`(" : "``(";
    }
    virtual void display(std::ostream & out) const override {
        out << prefix() << m_value << ")";
    }
    virtual unsigned hash() const override { return m_value.hash(); }
    virtual void write(serializer & s) const override { s << *g_expr_quote_opcode << m_value << m_reflected; }
    expr const & get_value() const { return m_value; }
    bool const & is_reflected() const { return m_reflected; }
};

expr mk_elaborated_expr_quote(expr const & e) {
    return mk_macro(macro_definition(new expr_quote_macro(e, /* reflected */ true)));
}
expr mk_unelaborated_expr_quote(expr const & e) {
    // We use a transparent annotation instead of the opaque macro above so that the quoted term is accessible to
    // collect_locals etc.
    return mk_annotation(*g_expr_quote_pre, e);
}
expr mk_pexpr_quote(expr const & e) {
    return mk_macro(macro_definition(new expr_quote_macro(e, /* reflected */ false)));
}

bool is_expr_quote(expr const & e) {
    if (is_annotation(e, *g_expr_quote_pre)) {
        return true;
    }
    if (is_macro(e)) {
        if (auto m = dynamic_cast<expr_quote_macro const *>(macro_def(e).raw())) {
            return m->is_reflected();
        }
    }
    return false;
}
bool is_pexpr_quote(expr const & e) {
    if (is_macro(e)) {
        if (auto m = dynamic_cast<expr_quote_macro const *>(macro_def(e).raw())) {
            return !m->is_reflected();
        }
    }
    return false;
}

expr const & get_expr_quote_value(expr const & e) {
    lean_assert(is_expr_quote(e));
    if (auto m = dynamic_cast<expr_quote_macro const *>(macro_def(e).raw())) {
        return m->get_value();
    } else {
        return get_annotation_arg(e);
    }
}

expr const & get_pexpr_quote_value(expr const & e) {
    lean_assert(is_pexpr_quote(e));
    return static_cast<expr_quote_macro const *>(macro_def(e).raw())->get_value();
}

static name * g_antiquote = nullptr;

expr mk_antiquote(expr const & e) { return mk_annotation(*g_antiquote, e); }
bool is_antiquote(expr const & e) { return is_annotation(e, *g_antiquote); }
expr const & get_antiquote_expr(expr const & e) {
    lean_assert(is_antiquote(e));
    return get_annotation_arg(e);
}

static name * g_quote_fresh = nullptr;

expr mk_pexpr_quote_and_substs(expr const & e, bool is_strict) {
    name x("_x");
    name_generator ngen(*g_quote_fresh);
    buffer<expr> locals;
    buffer<expr> aqs;
    expr s = replace(e, [&](expr const & t, unsigned) {
            if (is_antiquote(t)) {
                expr local = mk_local(ngen.next(), x.append_after(locals.size() + 1),
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
    g_quote_fresh         = new name("_quote_fresh");
    register_name_generator_prefix(*g_quote_fresh);
    g_expr_quote_macro    = new name("expr_quote_macro");
    g_expr_quote_opcode   = new std::string("Quote");
    g_expr           = new expr(mk_app(Const(get_expr_name()), mk_bool_tt()));
    g_pexpr          = new expr(mk_app(Const(get_expr_name()), mk_bool_ff()));

    g_antiquote      = new name("antiquote");
    g_expr_quote_pre = new name("expr_quote_pre");
    register_annotation(*g_antiquote);
    register_annotation(*g_expr_quote_pre);

    register_macro_deserializer(*g_expr_quote_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    expr e; bool reflected;
                                    d >> e >> reflected;
                                    return mk_macro(macro_definition(new expr_quote_macro(e, reflected)));
                                });
}

void finalize_quote() {
    delete g_quote_fresh;
    delete g_expr_quote_pre;
    delete g_expr_quote_macro;
    delete g_expr_quote_opcode;
    delete g_expr;
    delete g_pexpr;
    delete g_antiquote;
}
}

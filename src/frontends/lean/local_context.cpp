/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "frontends/lean/local_context.h"

namespace lean {
/** \brief Given a list of local constants \c locals
              (x_n : A_n) ... (x_0 : A_0)
    and a term \c e
              t[x_0, ..., x_n]
    return
              t[#n, ..., #0]
*/
expr abstract_locals(expr const & e, list<expr> const & locals) {
    lean_assert(std::all_of(locals.begin(), locals.end(), [](expr const & e) { return closed(e) && is_local(e); }));
    if (!has_local(e))
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_local(m))
                return some_expr(m); // expression m does not contain local constants
            if (is_local(m)) {
                unsigned i = 0;
                for (expr const & l : locals) {
                    if (mlocal_name(l) == mlocal_name(m))
                        return some_expr(copy_tag(m, mk_var(offset + i)));
                    i++;
                }
            }
            return none_expr();
        });
}

local_context::local_context(name const & prefix):m_ngen(prefix) {}
local_context::local_context(name const & prefix, list<expr> const & ctx):
    m_ngen(prefix) {
    set_ctx(ctx);
}

void local_context::set_ctx(list<expr> const & ctx) {
    m_ctx = ctx;
    buffer<expr> tmp;
    list<expr> it = ctx;
    while (it) {
        tmp.push_back(abstract_locals(head(it), tail(it)));
        it = tail(it);
    }
    m_ctx_abstracted = to_list(tmp.begin(), tmp.end());
    lean_assert(std::all_of(m_ctx_abstracted.begin(), m_ctx_abstracted.end(), [](expr const & e) { return is_local(e); }));
}

expr local_context::pi_abstract_context(expr e, tag g) const {
    e = abstract_locals(e, m_ctx);
    for (expr const & l : m_ctx_abstracted)
        e = mk_pi(local_pp_name(l), mlocal_type(l), e, local_info(l)).set_tag(g);
    return e;
}

static expr apply_context_core(expr const & f, list<expr> const & ctx, tag g) {
    if (ctx)
        return mk_app(apply_context_core(f, tail(ctx), g), head(ctx)).set_tag(g);
    else
        return f;
}

expr local_context::apply_context(expr const & f, tag g) const {
    return apply_context_core(f, m_ctx, g);
}

expr local_context::mk_type_metavar(tag g) {
    name n = m_ngen.next();
    expr s = mk_sort(mk_meta_univ(m_ngen.next())).set_tag(g);
    expr t = pi_abstract_context(s, g);
    return ::lean::mk_metavar(n, t).set_tag(g);
}

expr local_context::mk_type_meta(tag g) {
    return apply_context(mk_type_metavar(g), g);
}

expr local_context::mk_metavar(optional<expr> const & type, tag g) {
    name n      = m_ngen.next();
    expr r_type = type ? *type : mk_type_meta(g);
    expr t      = pi_abstract_context(r_type, g);
    return ::lean::mk_metavar(n, t).set_tag(g);
}

expr local_context::mk_meta(optional<expr> const & type, tag g) {
    expr mvar = mk_metavar(type, g);
    expr meta = apply_context(mvar, g);
    m_mvar2meta.insert(mlocal_name(mvar), meta);
    return meta;
}

void local_context::add_local(expr const & l) {
    lean_assert(is_local(l));
    m_ctx_abstracted = cons(abstract_locals(l, m_ctx), m_ctx_abstracted);
    m_ctx            = cons(l, m_ctx);
    lean_assert(length(m_ctx) == length(m_ctx_abstracted));
    lean_assert(is_local(head(m_ctx_abstracted)));
}

optional<expr> local_context::find_meta(name const & n) const {
    if (auto it = m_mvar2meta.find(n))
        return some_expr(*it);
    else
        return none_expr();
}

list<expr> const & local_context::get_data() const {
    return m_ctx;
}

local_context::scope::scope(local_context & main):
    m_main(main), m_old_ctx(main.m_ctx), m_old_ctx_abstracted(main.m_ctx_abstracted) {}
local_context::scope::~scope() {
    m_main.m_ctx            = m_old_ctx;
    m_main.m_ctx_abstracted = m_old_ctx_abstracted;
}
}

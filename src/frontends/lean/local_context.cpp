/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "frontends/lean/local_context.h"

namespace lean {
local_context::local_context(name const & prefix, list<expr> const & ctx):
    m_ngen(prefix) {
    set_ctx(ctx);
}

void local_context::set_ctx(list<expr> const & ctx) {
    m_ctx = ctx;
    m_ctx_buffer.clear();
    m_ctx_domain_buffer.clear();
    to_buffer(ctx, m_ctx_buffer);
    std::reverse(m_ctx_buffer.begin(), m_ctx_buffer.end());
    for (unsigned i = 0; i < m_ctx_buffer.size(); i++) {
        m_ctx_domain_buffer.push_back(abstract_locals(m_ctx_buffer[i], i, m_ctx_buffer.data()));
    }
}

expr local_context::pi_abstract_context(expr e, tag g) const {
    e = abstract_locals(e, m_ctx_buffer.size(), m_ctx_buffer.data());
    unsigned i = m_ctx_domain_buffer.size();
    while (i > 0) {
        --i;
        expr const & l = m_ctx_domain_buffer[i];
        e = mk_pi(local_pp_name(l), mlocal_type(l), e, local_info(l)).set_tag(g);
    }
    return e;
}

expr local_context::apply_context(expr const & f, tag g) const {
    expr r = f;
    for (unsigned i = 0; i < m_ctx_buffer.size(); i++)
        r = mk_app(r, m_ctx_buffer[i]).set_tag(g);
    return r;
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
    m_ctx = cons(l, m_ctx);
    m_ctx_domain_buffer.push_back(abstract_locals(l, m_ctx_buffer.size(), m_ctx_buffer.data()));
    m_ctx_buffer.push_back(l);
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
    m_main(main), m_old_ctx(main.m_ctx), m_old_sz(main.m_ctx_buffer.size()) {}
local_context::scope::~scope() {
    m_main.m_ctx = m_old_ctx;
    m_main.m_ctx_buffer.shrink(m_old_sz);
    m_main.m_ctx_domain_buffer.shrink(m_old_sz);
}
}

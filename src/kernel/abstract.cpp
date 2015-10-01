/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include <vector>
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "kernel/replace_fn.h"

namespace lean {
expr abstract(expr const & e, unsigned s, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, closed));
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            if (closed(e)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (subst[i] == e)
                        return some_expr(mk_var(offset + s + n - i - 1, e.get_tag()));
                }
            }
            return none_expr();
        });
}
expr abstract(expr const & e, unsigned n, expr const * subst) { return abstract(e, 0, n, subst); }
expr abstract(expr const & e, expr const & s, unsigned i) { return abstract(e, i, 1, &s); }

expr abstract_locals(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return closed(e) && is_local(e); }));
    if (!has_local(e))
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_local(m))
                return some_expr(m); // expression m does not contain local constants
            if (is_local(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (mlocal_name(subst[i]) == mlocal_name(m))
                        return some_expr(mk_var(offset + n - i - 1, m.get_tag()));
                }
                return none_expr();
            }
            return none_expr();
        });
}

expr abstract_local(expr const & e, name const & l) {
    expr dummy = mk_Prop();
    expr local = mk_local(l, dummy);
    return abstract_locals(e, 1, &local);
}

/**
   \brief Auxiliary datastructure for caching the types of locals constants after abstraction.
   It is very common to invoke mk_bindings(num, locals, b) with the same set of locals but
   different b's.
*/
class mk_binding_cache {
    std::vector<optional<expr>> m_locals;
    std::vector<optional<expr>> m_abstract_types;
public:
    mk_binding_cache() {}
    void abstract(unsigned num, expr const * locals, bool use_cache) {
        m_locals.resize(num, none_expr());
        m_abstract_types.resize(num, none_expr());
        bool matching = use_cache;
        for (unsigned i = 0; i < num; i++) {
            if (!(matching && m_locals[i] && *m_locals[i] == locals[i])) {
                m_locals[i]         = locals[i];
                m_abstract_types[i] = abstract_locals(mlocal_type(locals[i]), i, locals);
                matching            = false;
            }
        }
    }

    expr get_abstract_type(unsigned i) const {
        return *m_abstract_types[i];
    }

    void clear() {
        m_locals.clear();
        m_abstract_types.clear();
    }
};

MK_THREAD_LOCAL_GET_DEF(mk_binding_cache, get_mk_binding_cache);

template<bool is_lambda>
expr mk_binding(unsigned num, expr const * locals, expr const & b, bool use_cache) {
    expr r       = abstract_locals(b, num, locals);
    auto & cache = get_mk_binding_cache();
    cache.abstract(num, locals, use_cache);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = cache.get_abstract_type(i);
        if (is_lambda)
            r = mk_lambda(local_pp_name(l), t, r, local_info(l));
        else
            r = mk_pi(local_pp_name(l), t, r, local_info(l));
    }
    return r;
}

expr Pi(unsigned num, expr const * locals, expr const & b, bool use_cache) { return mk_binding<false>(num, locals, b, use_cache); }
expr Fun(unsigned num, expr const * locals, expr const & b, bool use_cache) { return mk_binding<true>(num, locals, b, use_cache); }

void clear_abstract_cache() {
    get_mk_binding_cache().clear();
}
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <algorithm>
#include "var_changer.h"
#include "free_vars.h"
#include "maps.h"

namespace lean {

template<typename FV, typename FS>
class var_changer_proc {
    expr_cell_offset_map<expr> m_cache;
    FV                         m_fv;
    FS                         m_fs;
public:
    var_changer_proc(FV const & fv, FS const & fs):
        m_fv(fv),
        m_fs(fs) {
    }

    expr apply(expr const & e, unsigned offset) {
        if (is_shared(e)) {
            expr_cell_offset p(e.raw(), offset);
            auto it = m_cache.find(p);
            if (it != m_cache.end())
                return it->second;
        }

        expr r = m_fs(e, offset);
        if (eqp(e, r)) {
            switch (e.kind()) {
            case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral: case expr_kind::Constant:
                break;
            case expr_kind::Var:
                r = m_fv(e, offset);
                break;
            case expr_kind::App: {
                std::vector<expr> new_args;
                bool modified = false;
                for (expr const & a : args(e)) {
                    new_args.push_back(apply(a, offset));
                    if (!eqp(a, new_args.back()))
                        modified = true;
                }
                if (modified)
                    r = app(new_args.size(), new_args.data());
                else
                    r = e;
                break;
            }
            case expr_kind::Lambda:
            case expr_kind::Pi: {
                expr const & old_t = abst_type(e);
                expr const & old_b = abst_body(e);
                expr t = apply(old_t, offset);
                expr b = apply(old_b, offset+1);
                if (!eqp(t, old_t) || !eqp(b, old_b)) {
                    name const & n = abst_name(e);
                    r = is_pi(e) ? pi(n, t, b) : lambda(n, t, b);
                }
                else {
                    r = e;
                }
                break;
            }}
        }

        if (is_shared(e))
            m_cache.insert(std::make_pair(expr_cell_offset(e.raw(), offset), r));

        return r;
    }
};

expr abstract(unsigned n, expr const * s, expr const & e) {
    lean_assert(std::all_of(s, s+n, closed));

    auto fv = [](expr const & x, unsigned offset) { return x; };

    auto fs = [=](expr const & e, unsigned offset) {
        unsigned i = n;
        while (i > 0) {
            --i;
            if (s[i] == e)
                return var(offset + n - i - 1);
        }
        return e;
    };

    var_changer_proc<decltype(fv), decltype(fs)> proc(fv, fs);
    return proc.apply(e, 0);
}

expr abstract_p(unsigned n, expr const * s, expr const & e) {
    lean_assert(std::all_of(s, s+n, closed));

    auto fv = [](expr const & x, unsigned offset) { return x; };

    auto fs = [=](expr const & e, unsigned offset) {
        unsigned i = n;
        while (i > 0) {
            --i;
            if (eqp(s[i], e))
                return var(offset + n - i - 1);
        }
        return e;
    };

    var_changer_proc<decltype(fv), decltype(fs)> proc(fv, fs);
    return proc.apply(e, 0);
}

expr instantiate(unsigned n, expr const * s, expr const & e) {
    lean_assert(std::all_of(s, s+n, closed));

    auto fv = [=](expr const & x, unsigned offset) {
        lean_assert(is_var(x));
        unsigned vidx = var_idx(x);
        if (vidx >= offset) {
            if (vidx < offset + n)
                return s[n - (vidx - offset) - 1];
            else
                return var(vidx - n);
        }
        else {
            return x;
        }
    };

    auto fs = [](expr const & c, unsigned offset) { return c; };

    var_changer_proc<decltype(fv), decltype(fs)> proc(fv, fs);
    return proc.apply(e, 0);
}

}

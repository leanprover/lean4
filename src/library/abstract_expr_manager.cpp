/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/abstract_expr_manager.h"
#include "kernel/instantiate.h"
#include "util/safe_arith.h"
#include "util/list_fn.h"

namespace lean {

unsigned abstract_expr_manager::hash(expr const & e) {
    unsigned h;
    switch (e.kind()) {
    case expr_kind::Constant:
    case expr_kind::Local:
    case expr_kind::Meta:
    case expr_kind::Sort:
    case expr_kind::Var:
    case expr_kind::Macro:
        return e.hash();
    case expr_kind::Lambda:
    case expr_kind::Pi:
        h = hash(binding_domain(e));
        // Remark binding_domain(e) may contain de-bruijn variables.
        // We can instantiate them eagerly as we do here, or lazily.
        // The lazy approach is potentially more efficient, but we would have
        // to use something more sophisticated than an instantiate_rev at expr_kind::App
        m_locals.push_back(instantiate_rev(m_tctx.mk_tmp_local(binding_domain(e)), m_locals.size(), m_locals.data()));
        h = ::lean::hash(h, hash(binding_body(e)));
        m_locals.pop_back();
        return h;
    case expr_kind::App:
        buffer<expr> args;
        expr f = instantiate_rev(get_app_args(e, args), m_locals.size(), m_locals.data());
        optional<congr_lemma> f_congr = m_congr_lemma_manager.mk_congr(f, args.size());
        h = hash(f);
        if (!f_congr) {
            for (expr const & arg : args) h = ::lean::hash(h, hash(arg));
        } else {
            int i = -1;
            for_each(f_congr->get_arg_kinds(), [&](congr_arg_kind const & c_kind) {
                    i++;
                    if (c_kind == congr_arg_kind::Cast) return;
                    h = ::lean::hash(h, hash(args[i]));
                });
        }
        return h;
    }
    lean_unreachable();
}

bool abstract_expr_manager::is_equal(expr const & a, expr const & b) {
        if (is_eqp(a, b))          return true;
        if (hash(a) != hash(b))    return false;
        if (a.kind() != b.kind())  return false;
        if (is_var(a))             return var_idx(a) == var_idx(b);
        bool is_eq;
        switch (a.kind()) {
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Constant: case expr_kind::Sort:
            return a == b;
        case expr_kind::Meta: case expr_kind::Local:
            return mlocal_name(a) == mlocal_name(b) && is_equal(mlocal_type(a), mlocal_type(b));
        case expr_kind::Lambda: case expr_kind::Pi:
            if (!is_equal(binding_domain(a), binding_domain(b))) return false;
            // see comment at abstract_expr_manager::hash
            m_locals.push_back(instantiate_rev(m_tctx.mk_tmp_local(binding_domain(a)), m_locals.size(), m_locals.data()));
            is_eq = is_equal(binding_body(a), binding_body(b));
            m_locals.pop_back();
            return is_eq;
        case expr_kind::Macro:
            if (macro_def(a) != macro_def(b) || macro_num_args(a) != macro_num_args(b))
                return false;
            for (unsigned i = 0; i < macro_num_args(a); i++) {
                if (!is_equal(macro_arg(a, i), macro_arg(b, i)))
                    return false;
            }
            return true;
        case expr_kind::App:
            buffer<expr> a_args, b_args;
            expr f_a = get_app_args(a, a_args);
            expr f_b = get_app_args(b, b_args);
            if (!is_equal(f_a, f_b)) return false;
            if (a_args.size() != b_args.size()) return false;
            expr f = instantiate_rev(f_a, m_locals.size(), m_locals.data());
            optional<congr_lemma> f_congr = m_congr_lemma_manager.mk_congr(f, a_args.size());
            bool not_equal = false;
            if (!f_congr) {
                for (unsigned i = 0; i < a_args.size(); ++i) {
                    if (!is_equal(a_args[i], b_args[i])) {
                        not_equal = true;
                        break;
                    }
                }
            } else {
                int i = -1;
                for_each(f_congr->get_arg_kinds(), [&](congr_arg_kind const & c_kind) {
                        if (not_equal) return;
                        i++;
                        if (c_kind == congr_arg_kind::Cast) return;
                        if (!is_equal(a_args[i], b_args[i])) not_equal = true;
                    });
            }
            return !not_equal;
        }
        lean_unreachable(); // LCOV_EXCL_LINE
}

}

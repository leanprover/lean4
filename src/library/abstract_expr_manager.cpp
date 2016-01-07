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
        // TODO(Leo): in the past we only had to apply instantiate_rev to the function.
        // We have to improve this.
        // One idea is to compute and cache the specialization prefix for f.
        // Then, we only need to apply instantiate_rev to f + prefix.
        // expr f = instantiate_rev(get_app_args(e, args), m_locals.size(), m_locals.data());
        expr new_e = instantiate_rev(e, m_locals.size(), m_locals.data());
        optional<congr_lemma> f_congr = m_congr_lemma_manager.mk_specialized_congr(new_e);
        buffer<expr> args;
        expr const & f = get_app_args(new_e, args);
        h = hash(f);
        if (!f_congr) {
            for (expr const & arg : args)  {
                h = ::lean::hash(h, hash(arg));
            }
        } else {
            unsigned i = 0;
            for_each(f_congr->get_arg_kinds(), [&](congr_arg_kind const & c_kind) {
                    if (c_kind != congr_arg_kind::Cast) {
                        h = ::lean::hash(h, hash(args[i]));
                    }
                    i++;
                });
        }
        return h;
    }
    lean_unreachable();
}

bool abstract_expr_manager::is_equal(expr const & a, expr const & b) {
    if (is_eqp(a, b))          return true;
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
        if (!is_equal(get_app_fn(a), get_app_fn(b))) {
            return false;
        }
        if (get_app_num_args(a) != get_app_num_args(b)) {
            return false;
        }
        // See comment in the hash function
        expr new_a = instantiate_rev(a, m_locals.size(), m_locals.data());
        expr new_b = instantiate_rev(b, m_locals.size(), m_locals.data());
        optional<congr_lemma> congra = m_congr_lemma_manager.mk_specialized_congr(new_a);
        optional<congr_lemma> congrb = m_congr_lemma_manager.mk_specialized_congr(new_b);
        buffer<expr> a_args, b_args;
        get_app_args(new_a, a_args);
        get_app_args(new_b, b_args);
        bool not_equal = false;
        if (!congra || !congrb) {
            for (unsigned i = 0; i < a_args.size(); ++i) {
                if (!is_equal(a_args[i], b_args[i])) {
                    not_equal = true;
                    break;
                }
            }
        } else {
            unsigned i = 0;
            for_each2(congra->get_arg_kinds(),
                      congrb->get_arg_kinds(),
                      [&](congr_arg_kind const & ca_kind, congr_arg_kind const & cb_kind) {
                          if (not_equal)
                              return;
                          if (ca_kind != cb_kind || (ca_kind != congr_arg_kind::Cast && !is_equal(a_args[i], b_args[i]))) {
                              not_equal = true;
                          }
                          i++;
                      });
        }
        return !not_equal;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}

/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/abstract_expr_manager.h"
#include "util/safe_arith.h"

namespace lean {

unsigned abstract_expr_manager::get_weight(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Constant:
    case expr_kind::Local:
    case expr_kind::Meta:
    case expr_kind::Sort:
    case expr_kind::Var:
    case expr_kind::Macro:        
        return ::lean::get_weight(e);
    case expr_kind::Lambda:
    case expr_kind::Pi:        
        return safe_add(1,safe_add(get_weight(binding_domain(e)), get_weight(binding_body(e))));
    case expr_kind::App:
        buffer<expr> args;
        expr f = get_app_args(e, args);
        fun_info f_info = m_fun_info_manager.get(f, args.size());
        unsigned w = get_weight(f);
        unsigned one = 1;
        int i = -1;
        for_each(f_info.get_params_info(), [&](param_info const & p_info) {
                i++;
                w = safe_add(w, one);
                if (p_info.is_subsingleton()) return;
                w = safe_add(w, get_weight(args[i]));
            });
        return w;
    }
    lean_unreachable();
}

unsigned abstract_expr_manager::hash(expr const & e) {
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
        return ::lean::hash(hash(binding_domain(e)), hash(binding_body(e)));
    case expr_kind::App:
        buffer<expr> args;
        expr f = get_app_args(e, args);
        fun_info f_info = m_fun_info_manager.get(f, args.size());
        unsigned h = hash(f);
        int i = -1;
        for_each(f_info.get_params_info(), [&](param_info const & p_info) {
                i++;
                if (p_info.is_subsingleton()) return;
                h = ::lean::hash(h, hash(args[i]));
            });
        return h;
    }
    lean_unreachable();
}

bool abstract_expr_manager::is_equal(expr const & a, expr const & b) {
        if (is_eqp(a, b))          return true;
        if (hash(a) != hash(b))    return false;
        if (a.kind() != b.kind())  return false;
        if (is_var(a))             return var_idx(a) == var_idx(b);
        switch (a.kind()) {
        case expr_kind::Var:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::Constant: case expr_kind::Sort:
            return a == b;
        case expr_kind::Meta: case expr_kind::Local:
            return mlocal_name(a) == mlocal_name(b) && is_equal(mlocal_type(a), mlocal_type(b));
        case expr_kind::Lambda: case expr_kind::Pi:
            return is_equal(binding_domain(a), binding_domain(b)) && is_equal(binding_body(a), binding_body(b));
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
            fun_info f_info = m_fun_info_manager.get(f_a, a_args.size());
            int i = -1;
            bool not_equal = false;
            for_each(f_info.get_params_info(), [&](param_info const & p_info) {
                    i++;
                    if (p_info.is_subsingleton()) return;
                    if (!is_equal(a_args[i], b_args[i])) not_equal = true;
                });
            return !not_equal;
        }
        lean_unreachable(); // LCOV_EXCL_LINE
}

bool abstract_expr_manager::is_lt(expr const & a, expr const & b) {
    if (is_eqp(a, b))                    return false;
    unsigned wa = get_weight(a);
    unsigned wb = get_weight(b);
    if (wa < wb)                         return true;
    if (wa > wb)                         return false;
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    if (is_equal(a,b))                   return false;
    switch (a.kind()) {
    case expr_kind::Var:
    case expr_kind::Constant:
    case expr_kind::Sort:
        return a < b;
    case expr_kind::Local: case expr_kind::Meta:
        if (mlocal_name(a) != mlocal_name(b))
            return mlocal_name(a) < mlocal_name(b);
        else
            return is_lt(mlocal_type(a), mlocal_type(b));
    case expr_kind::Lambda: case expr_kind::Pi:
        if (!is_equal(binding_domain(a), binding_domain(b)))
            return is_lt(binding_domain(a), binding_domain(b));
        else
            return is_lt(binding_body(a), binding_body(b));
    case expr_kind::Macro:
        if (macro_def(a) != macro_def(b))
            return macro_def(a) < macro_def(b);
        if (macro_num_args(a) != macro_num_args(b))
            return macro_num_args(a) < macro_num_args(b);
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (!is_equal(macro_arg(a, i), macro_arg(b, i)))
                return is_lt(macro_arg(a, i), macro_arg(b, i));
        }
        return false;
    case expr_kind::App:
        list<expr> a_args, b_args;
        expr f_a = a;
        expr f_b = b;
        while (is_app(f_a) && is_app(f_b)) {
            a_args = cons(app_arg(f_a), a_args);
            b_args = cons(app_arg(f_b), b_args);
            f_a = app_fn(f_a);
            f_b = app_fn(f_b);
        }
        if (!is_equal(f_a, f_b)) return is_lt(f_a, f_b);
        fun_info f_info = m_fun_info_manager.get(f_a, length(a_args));
        bool lt = false;
        bool gt = false;
        for_each3(f_info.get_params_info(), a_args, b_args,
                  [&](param_info const & p_info, expr const & a_arg, expr const & b_arg) {
                if (lt || gt) return;
                if (p_info.is_subsingleton()) return;
                if (!is_equal(a_arg, b_arg)) {
                    if (is_lt(a_arg, b_arg)) lt = true;
                    else gt = true;
                }
            });
        return lt;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

}

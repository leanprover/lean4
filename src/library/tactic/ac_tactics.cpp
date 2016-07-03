/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/app_builder.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
struct flat_assoc_fn {
    type_context & m_ctx;
    expr           m_op;
    expr           m_assoc;

    flat_assoc_fn(type_context & ctx, expr const & op, expr const & assoc):
        m_ctx(ctx), m_op(op), m_assoc(assoc) {}

    bool is_op_app(expr const & e, expr & lhs, expr & rhs) {
        if (!is_app(e)) return false;
        expr const & fn1 = app_fn(e);
        if (!is_app(fn1)) return false;
        if (app_fn(fn1) != m_op) return false;
        lhs = app_arg(fn1);
        rhs = app_arg(e);
        return true;
    }

    bool is_op_app(expr const & e) {
        if (!is_app(e)) return false;
        expr const & fn1 = app_fn(e);
        if (!is_app(fn1)) return false;
        return app_fn(fn1) == m_op;
    }

    expr mk_assoc(expr const & a, expr const & b, expr const & c) {
        return mk_app(m_assoc, a, b, c);
    }

    expr mk_eq_refl(expr const & a) {
        return ::lean::mk_eq_refl(m_ctx, a);
    }

    expr mk_eq_trans(expr const & H1, expr const & H2) {
        return ::lean::mk_eq_trans(m_ctx, H1, H2);
    }

    expr mk_eq_trans(expr const & H1, optional<expr> const & H2) {
        if (!H2) return H1;
        return mk_eq_trans(H1, *H2);
    }

    expr mk_congr_arg(expr const & fn, expr const & H) {
        return ::lean::mk_congr_arg(m_ctx, fn, H);
    }

    pair<expr, optional<expr>> flat_with(expr const & e, expr const & rest) {
        expr lhs, rhs;
        if (is_op_app(e, lhs, rhs)) {
            auto p1 = flat_with(rhs, rest);
            if (p1.second) {
                auto p2 = flat_with(lhs, p1.first);
                // H3 is a proof for (lhs `op` rhs) `op` rest = lhs `op` (rhs `op` rest)
                expr H3 = mk_assoc(lhs, rhs, rest);
                // H4 is a proof for lhs `op` (rhs `op` rest) = lhs `op` p1.first
                expr H4 = mk_congr_arg(mk_app(m_op, lhs), *p1.second);
                expr H  = mk_eq_trans(mk_eq_trans(H3, H4), p2.second);
                return mk_pair(p2.first, some_expr(H));
            } else {
                if (is_op_app(lhs)) {
                    auto p2 = flat_with(lhs, p1.first);
                    // H3 is a proof for (lhs `op` rhs) `op` rest = lhs `op` (rhs `op` rest)
                    expr H3 = mk_assoc(lhs, rhs, rest);
                    expr H  = mk_eq_trans(H3, p2.second);
                    return mk_pair(p2.first, some_expr(H));
                } else {
                    return mk_pair(mk_app(m_op, lhs, p1.first), some_expr(mk_assoc(lhs, rhs, rest)));
                }
            }
        } else {
            return mk_pair(mk_app(m_op, e, rest), none_expr());
        }
    }

    pair<expr, optional<expr>> flat_core(expr const & e) {
        expr lhs, rhs;
        if (is_op_app(e, lhs, rhs)) {
            auto p1 = flat_core(rhs);
            if (p1.second) {
                if (is_op_app(lhs)) {
                    auto p2 = flat_with(lhs, p1.first);
                    expr H3 = mk_congr_arg(mk_app(m_op, lhs), *p1.second);
                    expr H  = mk_eq_trans(H3, p2.second);
                    return mk_pair(p2.first, some_expr(H));
                } else {
                    expr r = mk_app(m_op, lhs, p1.first);
                    expr H = mk_congr_arg(mk_app(m_op, lhs), *p1.second);
                    return mk_pair(r, some_expr(H));
                }
            } else {
                if (is_op_app(lhs)) {
                    return flat_with(lhs, rhs);
                } else {
                    return mk_pair(e, none_expr());
                }
            }
        } else {
            return mk_pair(e, none_expr());
        }
    }

    pair<expr, expr> flat(expr const & e) {
        auto p = flat_core(e);
        if (p.second) {
            return mk_pair(p.first, *p.second);
        } else {
            return mk_pair(e, mk_eq_refl(e));
        }
    }
};

pair<expr, optional<expr>> flat_assoc(type_context & ctx, expr const & op, expr const & assoc, expr const & e) {
    return flat_assoc_fn(ctx, op, assoc).flat_core(e);
}

#define TRY   LEAN_TACTIC_TRY
#define CATCH LEAN_TACTIC_CATCH(to_tactic_state(s))

vm_obj tactic_flat_assoc(vm_obj const & op, vm_obj const & assoc, vm_obj const & e, vm_obj const & s) {
    TRY;
    type_context ctx   = mk_type_context_for(s);
    pair<expr, expr> p = flat_assoc_fn(ctx, to_expr(op), to_expr(assoc)).flat(to_expr(e));
    return mk_tactic_success(mk_vm_pair(to_obj(p.first), to_obj(p.second)), to_tactic_state(s));
    CATCH;
}

void initialize_ac_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "flat_assoc"}), tactic_flat_assoc);
}

void finalize_ac_tactics() {
}
}

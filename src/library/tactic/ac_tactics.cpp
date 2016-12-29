/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/app_builder.h"
#include "library/class.h"
#include "library/constants.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/ac_tactics.h"

namespace lean {
struct ac_manager::cache {
    environment                     m_env;
    unsigned                        m_reducibility_fingerprint;
    unsigned                        m_instance_fingerprint;
    expr_struct_map<optional<expr>> m_assoc_cache[2];
    expr_struct_map<optional<expr>> m_comm_cache[2];
    cache(environment const & env):
        m_env(env),
        m_reducibility_fingerprint(get_reducibility_fingerprint(env)),
        m_instance_fingerprint(get_instance_fingerprint(env)) {}
};

MK_THREAD_LOCAL_GET_DEF(ac_manager::cache_ptr, get_cache_ptr);

static ac_manager::cache_ptr get_cache(environment const & env) {
    auto & cache_ptr = get_cache_ptr();
    if (!cache_ptr ||
        !env.is_descendant(cache_ptr->m_env) ||
        get_reducibility_fingerprint(env) != cache_ptr->m_reducibility_fingerprint ||
        get_instance_fingerprint(env)     != cache_ptr->m_instance_fingerprint) {
        cache_ptr.reset();
        return std::make_shared<ac_manager::cache>(env);
    }
    ac_manager::cache_ptr r = cache_ptr;
    cache_ptr.reset();
    r->m_env = env;
    if (!is_eqp_declarations(env, r->m_env)) {
        /* erase cache for expressions containing locals, since it is probably not useful. */
        r->m_assoc_cache[1].clear();
        r->m_comm_cache[1].clear();
    }
    return r;
}

static void recycle_cache(ac_manager::cache_ptr const & cache) {
    get_cache_ptr() = cache;
}

ac_manager::ac_manager(type_context & ctx):
    m_ctx(ctx),
    m_cache_ptr(get_cache(ctx.env())) {
}

ac_manager::~ac_manager() {
    recycle_cache(m_cache_ptr);
}

optional<expr> ac_manager::is_assoc(expr const & e) {
    auto op = get_binary_op(e);
    if (!op) return none_expr();
    bool idx = has_local(e);
    auto it  = m_cache_ptr->m_assoc_cache[idx].find(*op);
    if (it != m_cache_ptr->m_assoc_cache[idx].end())
        return it->second;
    optional<expr> r;
    try {
        expr assoc_class = mk_app(m_ctx, get_is_associative_name(), *op);
        if (auto assoc_inst = m_ctx.mk_class_instance(assoc_class))
            r = some_expr(mk_app(m_ctx, get_is_associative_assoc_name(), 3, *op, *assoc_inst));
    } catch (app_builder_exception & ex) {}
    m_cache_ptr->m_assoc_cache[idx].insert(mk_pair(*op, r));
    return r;
}

optional<expr> ac_manager::is_comm(expr const & e) {
    auto op = get_binary_op(e);
    if (!op) return none_expr();
    bool idx = has_local(e);
    auto it  = m_cache_ptr->m_comm_cache[idx].find(*op);
    if (it != m_cache_ptr->m_comm_cache[idx].end())
        return it->second;
    optional<expr> r;
    try {
        expr comm_class = mk_app(m_ctx, get_is_commutative_name(), *op);
        if (auto comm_inst = m_ctx.mk_class_instance(comm_class))
            r = some_expr(mk_app(m_ctx, get_is_commutative_comm_name(), 3, *op, *comm_inst));
    } catch (app_builder_exception & ex) {}
    m_cache_ptr->m_comm_cache[idx].insert(mk_pair(*op, r));
    return r;
}

struct flat_assoc_fn {
    abstract_type_context & m_ctx;
    expr                    m_op;
    expr                    m_assoc;

    flat_assoc_fn(abstract_type_context & ctx, expr const & op, expr const & assoc):
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

    expr mk_op(expr const & a, expr const & b) {
        return mk_app(m_op, a, b);
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

    optional<expr> mk_eq_trans(optional<expr> const & H1, optional<expr> const & H2) {
        if (!H1) return H2;
        if (!H2) return H1;
        return some_expr(mk_eq_trans(*H1, *H2));
    }

    expr mk_eq_symm(expr const & H) {
        return ::lean::mk_eq_symm(m_ctx, H);
    }

    optional<expr> mk_eq_symm(optional<expr> const & H) {
        if (!H) return none_expr();
        return some_expr(mk_eq_symm(*H));
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
                    return mk_pair(mk_op(lhs, p1.first), some_expr(mk_assoc(lhs, rhs, rest)));
                }
            }
        } else {
            return mk_pair(mk_op(e, rest), none_expr());
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
                    expr r = mk_op(lhs, p1.first);
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

#define lean_perm_ac_trace(code) lean_trace(name({"tactic", "perm_ac"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); code)

struct perm_ac_fn : public flat_assoc_fn {
    expr           m_comm;
    optional<expr> m_left_comm;

    perm_ac_fn(abstract_type_context & ctx, expr const & op, expr const & assoc, expr const & comm):
        flat_assoc_fn(ctx, op, assoc), m_comm(comm) {
    }

    [[ noreturn ]] void throw_failed() {
        throw exception("perm_ac failed, arguments are not equal modulo AC");
    }

    expr mk_comm(expr const & a, expr const & b) {
        return mk_app(m_comm, a, b);
    }

    expr mk_left_comm(expr const & a, expr const & b, expr const & c) {
        if (!m_left_comm) {
            expr A    = m_ctx.infer(a);
            level lvl = get_level(m_ctx, A);
            m_left_comm = mk_app(mk_constant(get_left_comm_name(), {lvl}), A, m_op, m_comm, m_assoc);
        }
        return mk_app(*m_left_comm, a, b, c);
    }

    /* Given a term \c e of the form (op t_1 (op t_2 ... (op t_{n-1} t_n))), if
       for some i, t_i == t, then produce the term

           (op t_i (op t_2 ... (op t_{n-1} t_n)))

       and a proof they are equal AC.
       Throw exception if t is not found. */
    pair<expr, expr> pull_term(expr const & t, expr const & e) {
        expr lhs1, rhs1;
        if (!is_op_app(e, lhs1, rhs1)) {
            lean_perm_ac_trace(tout() << "right-hand-side does not contain:\n" << t << "\n";);
            throw_failed();
        }
        if (t == rhs1) {
            return mk_pair(mk_op(rhs1, lhs1), mk_comm(lhs1, rhs1));
        }
        expr lhs2, rhs2;
        if (!is_op_app(rhs1, lhs2, rhs2)) {
            lean_perm_ac_trace(tout() << "right-hand-side does not contain:\n" << t << "\n";);
            throw_failed();
        }
        if (t == lhs2) {
            return mk_pair(mk_op(lhs2, mk_op(lhs1, rhs2)), mk_left_comm(lhs1, lhs2, rhs2));
        }
        /* We have  e := lhs1 `op` lhs2 `op` rhs2 */
        auto p = pull_term(t, rhs1);
        expr lhs3, rhs3;
        lean_verify(is_op_app(p.first, lhs3, rhs3));
        lean_assert(t == lhs3);
        /* p.second : rhs1 = t `op` rhs3 */
        expr H1 = mk_congr_arg(mk_app(m_op, lhs1), p.second);
        /* H1 : lhs1 `op` rhs1 = lhs1 `op` t `op` rhs3 */
        expr H2 = mk_left_comm(lhs1, t, rhs3);
        /* H2 : lhs1 `op` t `op` rhs3 = t `op` lhs1 `op` rhs3 */
        return mk_pair(mk_op(t, mk_op(lhs1, rhs3)), mk_eq_trans(H1, H2));
    }

    /* Return a proof that e1 == e2 modulo AC. Return none if reflexivity.
       Throw exception if failure */
    optional<expr> perm_flat(expr const & e1, expr const & e2) {
        expr lhs1, rhs1;
        expr lhs2, rhs2;
        bool b1 = is_op_app(e1, lhs1, rhs1);
        bool b2 = is_op_app(e2, lhs2, rhs2);
        if (b1 != b2) {
            lean_perm_ac_trace(tout() << "left and right-hand-sides have different number of terms\n";);
            throw_failed();
        }
        if (!b1 && !b2) {
            if (e1 == e2) {
                return none_expr(); // reflexivity
            } else {
                lean_perm_ac_trace(tout() << "the left and right hand sides contain the terms:\n" << e1 << "\n" << e2 << "\n";);
                throw_failed();
            }
        }
        lean_assert(b1 && b2);
        if (lhs1 == lhs2) {
            optional<expr> H = perm_flat(rhs1, rhs2);
            if (!H) return none_expr();
            return some_expr(mk_congr_arg(mk_app(m_op, lhs1), *H));
        } else {
            auto p = pull_term(lhs2, e1);
            is_op_app(p.first, lhs1, rhs1);
            lean_assert(lhs1 == lhs2);
            optional<expr> H1 = perm_flat(rhs1, rhs2);
            if (!H1) return some_expr(p.second);
            expr H2 = mk_congr_arg(mk_app(m_op, lhs1), *H1);
            return some_expr(mk_eq_trans(p.second, H2));
        }
    }

    /* Return a proof that lhs == rhs modulo AC. Return none if reflexivity.
       Throw exception if failure */
    optional<expr> perm_core(expr const & lhs, expr const & rhs) {
        auto p1 = flat_core(lhs);
        auto p2 = flat_core(rhs);
        auto H  = perm_flat(p1.first, p2.first);
        return mk_eq_trans(p1.second, mk_eq_trans(H, mk_eq_symm(p2.second)));
    }

    expr perm(expr const & lhs, expr const & rhs) {
        if (auto H = perm_core(lhs, rhs))
            return *H;
        else
            return mk_eq_refl(lhs);
    }
};


pair<expr, optional<expr>> flat_assoc(abstract_type_context & ctx, expr const & op, expr const & assoc, expr const & e) {
    return flat_assoc_fn(ctx, op, assoc).flat_core(e);
}

expr perm_ac(abstract_type_context & ctx, expr const & op, expr const & assoc, expr const & comm, expr const & e1, expr const & e2) {
    return perm_ac_fn(ctx, op, assoc, comm).perm(e1, e2);
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

vm_obj tactic_perm_ac(vm_obj const & op, vm_obj const & assoc, vm_obj const & comm, vm_obj const & e1, vm_obj const & e2, vm_obj const & s) {
    TRY;
    type_context ctx   = mk_type_context_for(s);
    expr H = perm_ac_fn(ctx, to_expr(op), to_expr(assoc), to_expr(comm)).perm(to_expr(e1), to_expr(e2));
    return mk_tactic_success(to_obj(H), to_tactic_state(s));
    CATCH;
}

void initialize_ac_tactics() {
    register_trace_class(name{"tactic", "perm_ac"});
    DECLARE_VM_BUILTIN(name({"tactic", "flat_assoc"}), tactic_flat_assoc);
    DECLARE_VM_BUILTIN(name({"tactic", "perm_ac"}),    tactic_perm_ac);
}

void finalize_ac_tactics() {
}
}

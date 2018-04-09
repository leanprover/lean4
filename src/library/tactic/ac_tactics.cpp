/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include "kernel/expr_maps.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/app_builder.h"
#include "library/class.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/ac_tactics.h"

namespace lean {
struct ac_manager_old::cache {
    environment              m_env;
    expr_map<optional<expr>> m_assoc_cache[2];
    expr_map<optional<expr>> m_comm_cache[2];
    cache(environment const & env):
        m_env(env) {
    }
    void clear() {
        for (unsigned i = 0; i < 2; i++) {
            m_assoc_cache[i].clear();
            m_comm_cache[i].clear();
        }
    }
};

static ac_manager_old::cache_ptr get_cache(environment const & env) {
    return std::make_shared<ac_manager_old::cache>(env);
}

ac_manager_old::ac_manager_old(type_context_old & ctx):
    m_ctx(ctx),
    m_cache_ptr(get_cache(ctx.env())) {
}

ac_manager_old::~ac_manager_old() {
}

optional<expr> ac_manager_old::is_assoc(expr const & e) {
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

optional<expr> ac_manager_old::is_comm(expr const & e) {
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

static name * g_ac_app_name = nullptr;
static macro_definition * g_ac_app_macro = nullptr;
static std::string * g_ac_app_opcode = nullptr;

static expr expand_ac_core(expr const & e) {
    unsigned nargs = macro_num_args(e);
    unsigned i     = nargs - 1;
    expr const & op = macro_arg(e, i);
    --i;
    expr r = macro_arg(e, i);
    while (i > 0) {
        --i;
        r = mk_app(op, macro_arg(e, i), r);
    }
    return r;
}

class ac_app_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_ac_app_name; }

    virtual unsigned trust_level() const { return LEAN_AC_MACROS_TRUST_LEVEL; }

    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return ctx.infer(macro_arg(e, 0));
    }

    virtual optional<expr> expand(expr const & e, abstract_type_context &) const {
        return some_expr(expand_ac_core(e));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_ac_app_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        ac_app_macro_cell const * other_ptr = dynamic_cast<ac_app_macro_cell const *>(&other);
        return other_ptr;
    }

    virtual unsigned hash() const { return 37; }
};

static expr mk_ac_app_core(unsigned nargs, expr const * args_op) {
    lean_assert(nargs >= 3);
    return mk_macro(*g_ac_app_macro, nargs, args_op);
}

static expr mk_ac_app_core(expr const & op, buffer<expr> & args) {
    lean_assert(args.size() >= 2);
    args.push_back(op);
    expr r = mk_ac_app_core(args.size(), args.data());
    args.pop_back();
    return r;
}

expr mk_ac_app(expr const & op, buffer<expr> & args) {
    lean_assert(args.size() > 0);
    if (args.size() == 1) {
        return args[0];
    } else {
        std::sort(args.begin(), args.end(), is_hash_lt);
        return mk_ac_app_core(op, args);
    }
}

bool is_ac_app(expr const & e) {
    return is_macro(e) && is_eqp(macro_def(e), *g_ac_app_macro);
}

expr const & get_ac_app_op(expr const & e) {
    lean_assert(is_ac_app(e));
    return macro_arg(e, macro_num_args(e) - 1);
}

unsigned get_ac_app_num_args(expr const & e) {
    lean_assert(is_ac_app(e));
    return macro_num_args(e) - 1;
}

expr const * get_ac_app_args(expr const & e) {
    lean_assert(is_ac_app(e));
    return macro_args(e);
}

/* Return true iff e1 occurs in e2.
   Example ac_mem(b, a*a*b*c) returns true. */
static bool ac_mem(expr const & e1, expr const & e2) {
    unsigned nargs2    = get_ac_app_num_args(e2);
    expr const * args2 = get_ac_app_args(e2);
    return std::find(args2, args2+nargs2, e1) != args2+nargs2;
}

/* Return true iff e1 is a "subset" of e2.
   Example: The result is true for e1 := (a*a*a*b*d) and e2 := (a*a*a*a*b*b*c*d*d) */
bool is_ac_subset(expr const & e1, expr const & e2) {
    if (is_ac_app(e1)) {
        if (is_ac_app(e2)) {
            if (get_ac_app_op(e1) == get_ac_app_op(e2)) {
                unsigned nargs1 = get_ac_app_num_args(e1);
                unsigned nargs2 = get_ac_app_num_args(e2);
                if (nargs1 > nargs2) return false;
                expr const * args1 = get_ac_app_args(e1);
                expr const * args2 = get_ac_app_args(e2);
                unsigned i1 = 0;
                unsigned i2 = 0;
                while (i1 < nargs1 && i2 < nargs2) {
                    if (args1[i1] == args2[i2]) {
                        i1++;
                        i2++;
                    } else if (is_hash_lt(args2[i2], args1[i1])) {
                        i2++;
                    } else {
                        lean_assert(is_hash_lt(args1[i1], args2[i2]));
                        return false;
                    }
                }
                return i1 == nargs1;
            } else {
                lean_assert(get_ac_app_op(e1) != get_ac_app_op(e2));
                /* treat e1 as an atomic value that may occur in e2 */
                return ac_mem(e1, e2);
            }
        } else {
            return false;
        }
    } else {
        if (is_ac_app(e2)) {
            return ac_mem(e1, e2);
        } else {
            return e1 == e2;
        }
    }
}

/* Store in r e1\e2.
   Example: given e1 := (a*a*a*a*b*b*c*d*d*d) and e2 := (a*a*a*b*b*d),
   the result is (a, c, d, d)

   \pre is_ac_subset(e2, e1) */
void ac_diff(expr const & e1, expr const & e2, buffer<expr> & r) {
    lean_assert(is_ac_subset(e2, e1));
    if (is_ac_app(e1)) {
        if (is_ac_app(e2) && get_ac_app_op(e1) == get_ac_app_op(e2)) {
            unsigned nargs1 = get_ac_app_num_args(e1);
            unsigned nargs2 = get_ac_app_num_args(e2);
            lean_assert(nargs1 >= nargs2);
            expr const * args1 = get_ac_app_args(e1);
            expr const * args2 = get_ac_app_args(e2);
            unsigned i2 = 0;
            for (unsigned i1 = 0; i1 < nargs1; i1++) {
                if (i2 == nargs2) {
                    r.push_back(args1[i1]);
                } else if (args1[i1] == args2[i2]) {
                    i2++;
                } else {
                    lean_assert(is_hash_lt(args1[i1], args2[i2]));
                    r.push_back(args1[i1]);
                }
            }
        } else {
            bool found = false;
            unsigned nargs1    = get_ac_app_num_args(e1);
            expr const * args1 = get_ac_app_args(e1);
            for (unsigned i = 0; i < nargs1; i++) {
                if (!found && args1[i] == e2) {
                    found = true;
                } else {
                    r.push_back(args1[i]);
                }
            }
            lean_assert(found);
        }
    } else {
        lean_assert(!is_ac_app(e1));
        lean_assert(!is_ac_app(e2));
        lean_assert(e1 == e2);
    }
}

void ac_append(expr const & op, expr const & e, buffer<expr> & r) {
    if (is_ac_app(e) && get_ac_app_op(e) == op) {
        r.append(get_ac_app_num_args(e), get_ac_app_args(e));
    } else {
        r.push_back(e);
    }
}

void ac_intersection(expr const & e1, expr const & e2, buffer<expr> & r) {
    lean_assert(is_ac_app(e1));
    lean_assert(is_ac_app(e2));
    lean_assert(get_ac_app_op(e1) == get_ac_app_op(e2));
    unsigned nargs1 = get_ac_app_num_args(e1);
    unsigned nargs2 = get_ac_app_num_args(e2);
    expr const * args1 = get_ac_app_args(e1);
    expr const * args2 = get_ac_app_args(e2);
    unsigned i1 = 0;
    unsigned i2 = 0;
    while (i1 < nargs1 && i2 < nargs2) {
        if (args1[i1] == args2[i2]) {
            r.push_back(args1[i1]);
            i1++;
            i2++;
        } else if (is_hash_lt(args2[i2], args1[i1])) {
            i2++;
        } else {
            lean_assert(is_hash_lt(args1[i1], args2[i2]));
            i1++;
        }
    }
}

expr mk_ac_flat_app(expr const & op, expr const & e1, expr const & e2) {
    buffer<expr> new_args;
    ac_append(op, e1, new_args);
    ac_append(op, e2, new_args);
    return mk_ac_app(op, new_args);
}

/* lexdeg order */
bool ac_lt(expr const & e1, expr const & e2) {
    if (is_ac_app(e1)) {
        if (is_ac_app(e2) && get_ac_app_op(e1) == get_ac_app_op(e2)) {
            unsigned nargs1 = get_ac_app_num_args(e1);
            unsigned nargs2 = get_ac_app_num_args(e2);
            if (nargs1 < nargs2) return true;
            if (nargs1 > nargs2) return false;
            expr const * args1 = get_ac_app_args(e1);
            expr const * args2 = get_ac_app_args(e2);
            for (unsigned i = 0; i < nargs1; i++) {
                if (args1[i] != args2[i])
                    return is_hash_lt(args1[i], args2[i]);
            }
            return false;
        } else {
            return false;
        }
    } else {
        if (is_ac_app(e2)) {
            return true;
        } else {
            return is_hash_lt(e1, e2);
        }
    }
}

static expr expand_if_ac_app(expr const & e) {
    if (is_ac_app(e))
        return expand_ac_core(e);
    else
        return e;
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
            lhs     = expand_if_ac_app(lhs);
            rhs     = expand_if_ac_app(rhs);
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

    pair<expr, optional<expr>> flat_core(expr e) {
        expr lhs, rhs;
        e = expand_if_ac_app(e);
        if (is_op_app(e, lhs, rhs)) {
            lhs = expand_if_ac_app(lhs);
            rhs = expand_if_ac_app(rhs);
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

    level dec_level(level const & l) {
        if (auto r = ::lean::dec_level(l))
            return *r;
        throw_failed();
    }

    expr mk_left_comm(expr const & a, expr const & b, expr const & c) {
        if (!m_left_comm) {
            expr A    = m_ctx.infer(a);
            level lvl = dec_level(get_level(m_ctx, A));
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

static name * g_perm_ac_name = nullptr;
static macro_definition * g_perm_ac_macro = nullptr;
static std::string * g_perm_ac_opcode = nullptr;

class perm_ac_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_perm_ac_name; }

    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return mk_eq(ctx, macro_arg(e, 2), macro_arg(e, 3));
    }

    virtual unsigned trust_level() const { return LEAN_AC_MACROS_TRUST_LEVEL; }

    virtual optional<expr> expand(expr const & e, abstract_type_context & ctx) const {
        expr const & assoc = macro_arg(e, 0);
        expr const & comm  = macro_arg(e, 1);
        expr e1            = expand_if_ac_app(macro_arg(e, 2));
        expr e2            = expand_if_ac_app(macro_arg(e, 3));
        expr const & op    = app_fn(app_fn(e1));
        return some_expr(perm_ac(ctx, op, assoc, comm, e1, e2));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_perm_ac_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        perm_ac_macro_cell const * other_ptr = dynamic_cast<perm_ac_macro_cell const *>(&other);
        return other_ptr;
    }

    virtual unsigned hash() const { return 31; }
};

expr mk_perm_ac_macro_core(expr const & assoc, expr const & comm, expr const & e1, expr const & e2) {
    lean_assert((get_binary_op(e1) || is_ac_app(e1)) && (get_binary_op(e2) || is_ac_app(e2)));
    expr args[4] = {assoc, comm, e1, e2};
    return mk_macro(*g_perm_ac_macro, 4, args);
}

expr mk_perm_ac_macro(abstract_type_context & ctx, expr const & assoc, expr const & comm, expr const & e1, expr const & e2) {
    if (e1 == e2) {
        return mk_eq_refl(ctx, e1);
    } else {
        return mk_perm_ac_macro_core(assoc, comm, e1, e2);
    }
}

#define TRY   LEAN_TACTIC_TRY
#define CATCH LEAN_TACTIC_CATCH(tactic::to_state(s))

vm_obj tactic_flat_assoc(vm_obj const & op, vm_obj const & assoc, vm_obj const & e, vm_obj const & s) {
    TRY;
    type_context_old ctx   = mk_type_context_for(s);
    pair<expr, expr> p = flat_assoc_fn(ctx, to_expr(op), to_expr(assoc)).flat(to_expr(e));
    return tactic::mk_success(mk_vm_pair(to_obj(p.first), to_obj(p.second)), tactic::to_state(s));
    CATCH;
}

vm_obj tactic_perm_ac(vm_obj const & op, vm_obj const & assoc, vm_obj const & comm, vm_obj const & e1, vm_obj const & e2, vm_obj const & s) {
    TRY;
    type_context_old ctx   = mk_type_context_for(s);
    expr H = perm_ac_fn(ctx, to_expr(op), to_expr(assoc), to_expr(comm)).perm(to_expr(e1), to_expr(e2));
    return tactic::mk_success(to_obj(H), tactic::to_state(s));
    CATCH;
}

void initialize_ac_tactics() {
    register_trace_class(name{"tactic", "perm_ac"});
    DECLARE_VM_BUILTIN(name({"tactic", "flat_assoc"}), tactic_flat_assoc);
    DECLARE_VM_BUILTIN(name({"tactic", "perm_ac"}),    tactic_perm_ac);

    g_ac_app_name   = new name("ac_app");
    g_ac_app_opcode = new std::string("ACApp");
    g_ac_app_macro  = new macro_definition(new ac_app_macro_cell());
    register_macro_deserializer(*g_ac_app_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    return mk_ac_app_core(num, args);
                                });

    g_perm_ac_name   = new name("perm_ac");
    g_perm_ac_opcode = new std::string("PermAC");
    g_perm_ac_macro  = new macro_definition(new perm_ac_macro_cell());
    register_macro_deserializer(*g_perm_ac_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 4) corrupted_stream_exception();
                                    return mk_perm_ac_macro_core(args[0], args[1], args[2], args[3]);
                                });
}

void finalize_ac_tactics() {
    delete g_ac_app_name;
    delete g_ac_app_opcode;
    delete g_ac_app_macro;

    delete g_perm_ac_name;
    delete g_perm_ac_opcode;
    delete g_perm_ac_macro;
}
}

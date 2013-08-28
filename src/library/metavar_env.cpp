/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <iomanip>
#include "metavar_env.h"
#include "name_set.h"
#include "free_vars.h"
#include "exception.h"
#include "for_each.h"
#include "replace.h"
#include "printer.h"
#include "beta.h"
#include "flet.h"

namespace lean {
static name g_metavar_prefix(name(name(name(0u), "library"), "metavar"));

expr mk_metavar(unsigned idx) {
    return mk_constant(name(g_metavar_prefix, idx));
}

bool is_metavar(expr const & n) {
    return is_constant(n) && !const_name(n).is_atomic() && const_name(n).get_prefix() == g_metavar_prefix;
}

unsigned metavar_idx(expr const & n) {
    lean_assert(is_metavar(n));
    return const_name(n).get_numeral();
}

struct found_metavar {};

bool has_metavar(expr const & e) {
    auto f = [](expr const & c, unsigned offset) {
        if (is_metavar(c))
            throw found_metavar();
    };
    try {
        for_each_fn<decltype(f)> proc(f);
        proc(e);
        return false;
    } catch (found_metavar) {
        return true;
    }
}

/** \brief Return true iff \c e contains a metavariable with index midx */
bool has_metavar(expr const & e, unsigned midx) {
    auto f = [=](expr const & m, unsigned offset) {
        if (is_metavar(m) && metavar_idx(m) == midx)
            throw found_metavar();
    };
    try {
        for_each_fn<decltype(f)> proc(f);
        proc(e);
        return false;
    } catch (found_metavar) {
        return true;
    }
}

metavar_env::cell::cell(expr const & e, unsigned ctx_size, unsigned find):
    m_expr(e),
    m_ctx_size(ctx_size),
    m_find(find),
    m_rank(0),
    m_state(state::Unprocessed) {
}

/** \brief Return true iff the cell midx is the root of its equivalence class */
bool metavar_env::is_root(unsigned midx) const {
    return m_cells[midx].m_find == midx;
}

/** \brief Return the root cell index of the equivalence class of \c midx */
unsigned metavar_env::root_midx(unsigned midx) const {
    while (!is_root(midx)) {
        midx = m_cells[midx].m_find;
    }
    return midx;
}

/** \brief Return the root cell of the equivalence class of \c midx */
metavar_env::cell & metavar_env::root_cell(unsigned midx) {
    return m_cells[root_midx(midx)];
}

metavar_env::cell const & metavar_env::root_cell(unsigned midx) const {
    return m_cells[root_midx(midx)];
}

/**
   \brief Return the root cell of the equivalence class of the
   metavariable \c m.

   \pre is_metavar(m)
*/
metavar_env::cell & metavar_env::root_cell(expr const & m) {
    lean_assert(is_metavar(m));
    return root_cell(metavar_idx(m));
}

metavar_env::cell const & metavar_env::root_cell(expr const & m) const {
    lean_assert(is_metavar(m));
    return root_cell(metavar_idx(m));
}

/** \brief Auxiliary function for computing the new rank of an equivalence class. */
unsigned metavar_env::new_rank(unsigned r1, unsigned r2) {
    if (r1 == r2) return r1 + 1;
    else return std::max(r1, r2);
}

[[noreturn]] void metavar_env::failed_to_unify() {
    throw exception("failed to unify");
}

metavar_env::metavar_env(environment const & env, name_set const * available_defs, unsigned max_depth):
    m_env(env) {
    m_available_definitions = available_defs;
    m_max_depth = max_depth;
    m_depth     = 0;
    m_interrupted = false;
    m_modified    = false;
}

metavar_env::metavar_env(environment const & env, name_set const * available_defs):
    metavar_env(env, available_defs, std::numeric_limits<unsigned>::max()) {
}

metavar_env::metavar_env(environment const & env):metavar_env(env, nullptr) {
}

expr metavar_env::mk_metavar(unsigned ctx_sz) {
    m_modified    = true;
    unsigned vidx = m_cells.size();
    expr m = ::lean::mk_metavar(vidx);
    m_cells.push_back(cell(m, ctx_sz, vidx));
    return m;
}

bool metavar_env::is_assigned(expr const & m) const {
    return !is_metavar(root_cell(m).m_expr);
}

expr metavar_env::root_at(expr const & e, unsigned ctx_size) const {
    if (is_metavar(e)) {
        cell const & c = root_cell(e);
        if (is_metavar(c.m_expr)) {
            return c.m_expr;
        } else {
            lean_assert(c.m_ctx_size <= ctx_size);
            return lift_free_vars(c.m_expr, ctx_size - c.m_ctx_size);
        }
    } else {
        return e;
    }
}

/**
   \brief Make sure that the metavariables in \c s can only access
   ctx_size free variables.

   \pre s does not contain assigned metavariables.
*/
void metavar_env::reduce_metavars_ctx_size(expr const & s, unsigned ctx_size) {
    auto proc = [&](expr const & m, unsigned offset) {
        if (is_metavar(m)) {
            lean_assert(!is_assigned(m));
            cell & mc = root_cell(m);
            if (mc.m_ctx_size > ctx_size + offset)
                mc.m_ctx_size = ctx_size + offset;
        }
    };
    for_each_fn<decltype(proc)> visitor(proc);
    visitor(s);
}

void metavar_env::assign(expr const & m, expr const & s, unsigned ctx_size) {
    lean_assert(is_metavar(m));
    lean_assert(!is_assigned(m));
    if (m == s)
        return;
    m_modified = true;
    cell & mc = root_cell(m);
    lean_assert(is_metavar(mc.m_expr));
    lean_assert(metavar_idx(mc.m_expr) == mc.m_find);
    expr _s = instantiate_metavars(s, ctx_size);
    if (is_metavar(_s)) {
        // both are unassigned meta-variables...
        lean_assert(!is_assigned(_s));
        cell & sc = root_cell(_s);
        lean_assert(is_metavar(sc.m_expr));
        unsigned new_ctx_sz = std::min(mc.m_ctx_size, sc.m_ctx_size);
        mc.m_ctx_size = new_ctx_sz;
        sc.m_ctx_size = new_ctx_sz;
        if (mc.m_rank > sc.m_rank) {
            // we want to make mc the root of the equivalence class.
            mc.m_rank    = new_rank(mc.m_rank, sc.m_rank);
            sc.m_find    = mc.m_find;
        } else {
            // sc is the root
            sc.m_rank  = new_rank(mc.m_rank, sc.m_rank);
            mc.m_find  = sc.m_find;
        }
    } else {
        lean_assert(!is_metavar(_s));
        if (has_metavar(_s, mc.m_find)) {
            failed_to_unify();
        }
        reduce_metavars_ctx_size(_s, mc.m_ctx_size);
        if (ctx_size < mc.m_ctx_size) {
            // mc is used in a context with more free variables.
            // but s free variables are references to a smaller context.
            // So, we must lift _s free variables.
            _s = lift_free_vars(_s, mc.m_ctx_size - ctx_size);
        } else if (ctx_size > mc.m_ctx_size) {
            // _s must only contain free variables that are available
            // in the context of mc
            if (has_free_var(_s, 0, ctx_size - mc.m_ctx_size)) {
                failed_to_unify();
            }
            _s = lower_free_vars(_s, ctx_size - mc.m_ctx_size);
        }
        mc.m_expr = _s;
    }
}

expr metavar_env::instantiate_metavars(expr const & e, unsigned outer_offset) {
    auto it = [&](expr const & c, unsigned offset) -> expr {
        if (is_metavar(c)) {
            unsigned midx = metavar_idx(c);
            if (midx < m_cells.size()) {
                cell & rc = root_cell(midx);
                if (is_metavar(rc.m_expr)) {
                    return rc.m_expr;
                } else {
                    switch (rc.m_state) {
                    case state::Unprocessed:
                        rc.m_state = state::Processing;
                        rc.m_expr  = instantiate_metavars(rc.m_expr, rc.m_ctx_size);
                        rc.m_state = state::Processed;
                        lean_assert(rc.m_ctx_size <= offset + outer_offset);
                        return lift_free_vars(rc.m_expr, offset + outer_offset - rc.m_ctx_size);
                    case state::Processing: throw exception("cycle detected");
                    case state::Processed:
                        lean_assert(rc.m_ctx_size <= offset + outer_offset);
                        return lift_free_vars(rc.m_expr, offset + outer_offset - rc.m_ctx_size);
                    }
                }
            }
        }
        return c;
    };

    replace_fn<decltype(it)> proc(it);
    return proc(e);
}

bool metavar_env::is_definition(expr const & e) {
    if (is_constant(e)) {
        name const & n = const_name(e);
        if (m_available_definitions && m_available_definitions->find(n) == m_available_definitions->end()) {
            return false;
        } else {
            object const & obj = m_env.find_object(const_name(e));
            return obj && obj.is_definition() && !obj.is_opaque();
        }
    } else {
        return false;
    }
}

expr const & metavar_env::get_definition(expr const & e) {
    lean_assert(is_definition(e));
    return m_env.find_object(const_name(e)).get_value();
}

// Little hack for matching (?m #0) with t
// TODO: implement some support for higher order unification.
bool metavar_env::is_simple_ho_match(expr const & e1, expr const & e2, context const & ctx) {
    if (is_app(e1) && is_metavar(arg(e1,0)) && is_var(arg(e1,1), 0) && num_args(e1) == 2 && length(ctx) > 0) {
        return true;
    } else {
        return false;
    }
}

// Little hack for matching (?m #0) with t
// TODO: implement some support for higher order unification.
void metavar_env::unify_simple_ho_match(expr const & e1, expr const & e2, unsigned ctx_size, context const & ctx) {
    unify(arg(e1,0), mk_lambda(car(ctx).get_name(), car(ctx).get_domain(), e2), ctx_size, ctx);
}

/**
   \brief Auxiliary function for unifying expressions \c e1 and
   \c e2 when none of them are metavariables.
*/
void metavar_env::unify_core(expr const & e1, expr const & e2, unsigned ctx_size, context const & ctx) {
    check_interrupted(m_interrupted);
    lean_assert(!is_metavar(e1));
    lean_assert(!is_metavar(e2));
    if (e1 == e2) {
        return;
    } else if (is_type(e1) && is_type(e2)) {
        return; // ignoring type universe levels. We let the kernel check that
    } else if (is_abstraction(e1) && is_abstraction(e2)) {
        unify(abst_domain(e1), abst_domain(e2), ctx_size, ctx);
        unify(abst_body(e1),   abst_body(e2), ctx_size+1, extend(ctx, abst_name(e1), abst_domain(e1)));
    } else if (is_eq(e1) && is_eq(e2)) {
        unify(eq_lhs(e1), eq_lhs(e2), ctx_size, ctx);
        unify(eq_rhs(e1), eq_rhs(e2), ctx_size, ctx);
    } else {
        expr r1 = head_reduce(e1, m_env, m_available_definitions);
        expr r2 = head_reduce(e2, m_env, m_available_definitions);
        if (!is_eqp(e1, r1) || !is_eqp(e2, r2)) {
            return unify(r1, r2, ctx_size, ctx);
        } else if (is_app(e1) && is_app(e2) && num_args(e1) == num_args(e2)) {
            unsigned num = num_args(e1);
            for (unsigned i = 0; i < num; i++) {
                unify(arg(e1, i), arg(e2, i), ctx_size, ctx);
            }
        } else if (is_simple_ho_match(e1, e2, ctx)) {
            unify_simple_ho_match(e1, e2, ctx_size, ctx);
        } else if (is_simple_ho_match(e2, e1, ctx)) {
            unify_simple_ho_match(e2, e1, ctx_size, ctx);
        } else {
            failed_to_unify();
        }
    }
}

void metavar_env::unify(expr const & e1, expr const & e2, unsigned ctx_size, context const & ctx) {
    lean_assert(ctx_size == length(ctx));
    flet<unsigned> l(m_depth, m_depth+1);
    if (m_depth > m_max_depth)
        throw exception("unifier maximum recursion depth exceeded");
    expr const & r1 = root_at(e1, ctx_size);
    expr const & r2 = root_at(e2, ctx_size);
    if (is_metavar(r1)) {
        assign(r1, r2, ctx_size);
    } else {
        if (is_metavar(r2)) {
            assign(r2, r1, ctx_size);
        } else {
            unify_core(r1, r2, ctx_size, ctx);
        }
    }
}

void metavar_env::unify(expr const & e1, expr const & e2, context const & ctx) {
    unify(e1, e2, length(ctx), ctx);
}

void metavar_env::set_interrupt(bool flag) {
    m_interrupted = flag;
}

void metavar_env::clear() {
    m_cells.clear();
}

void metavar_env::display(std::ostream & out) const {
    for (unsigned i = 0; i < m_cells.size(); i++) {
        out << "?" << i << " --> ";
        out << "?" << std::left << std::setw(4) << m_cells[i].m_find
            << std::left << std::setw(3) << m_cells[i].m_rank;
        cell const & c = root_cell(i);
        if (!is_metavar(c.m_expr))
            out << c.m_expr;
        else
            out << "[unassigned]";
        out << ", ctx_sz: " << c.m_ctx_size;
        out << "\n";
    }
}

bool metavar_env::check_invariant() const {
    for (unsigned i = 0; i < m_cells.size(); i++) {
        lean_assert(root_midx(i) == root_midx(m_cells[i].m_find));
        lean_assert(m_cells[i].m_rank <= root_cell(i).m_rank);
    }
    return true;
}
}
void print(lean::metavar_env const & env) { env.display(std::cout); }

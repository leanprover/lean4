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

metavar_env::cell::cell(expr const & e, context const & ctx, unsigned find):
    m_expr(e),
    m_context(ctx),
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

/**
   \brief Assign m <- s, where s is a term.

   \pre s contains only unassigned metavariables.

   The contexts of the unassigned metavariables occurring in s are
   shortened to the length of the context associated with m.

   The assignment is valid if:

   1) \c s does contain free variables outside of the context
   associated with m.

   2) \c s does not contain m.

   3) The context of every metavariable in s is unifiable with the
   context of m.
*/
void metavar_env::assign_term(expr const & m, expr s, context const & ctx) {
    lean_assert(is_metavar(m));
    lean_assert(!is_assigned(m));
    lean_assert(!is_metavar(s));
    cell & mc             = root_cell(m);
    unsigned len_mc       = length(mc.m_context);
    unsigned len_ctx      = length(ctx);
    if (len_ctx < len_mc) {
        // mc is used in a context with len_mc variables,
        // but s free variables are references to a smaller context.
        // So, we must lift s free variables.
        s = lift_free_vars(s, len_mc - len_ctx);
    } else if (len_ctx > len_mc) {
        // s must only contain free variables that are available in mc.m_context
        if (has_free_var(s, 0, len_ctx - len_mc))
            failed_to_unify();
        s = lower_free_vars(s, len_ctx - len_mc);
    }
    unsigned fv_range = 0;
    auto proc = [&](expr const & n, unsigned offset) {
        if (is_var(n)) {
            unsigned vidx = var_idx(n);
            if (vidx >= offset) {
                unsigned fv_idx = vidx - offset;
                fv_range        = std::max(fv_range, fv_idx+1);
            }
        } else if (is_metavar(n)) {
            // Remark: before performing an assignment, we
            // instantiate all assigned metavariables in s.
            lean_assert(!is_assigned(n));
            cell & nc = root_cell(n);
            if (mc.m_find == nc.m_find)
                failed_to_unify(); // cycle detected
            unsigned len_nc = length(nc.m_context);
            // make sure nc is not bigger than mc
            while (len_nc > len_mc) { nc.m_context = cdr(nc.m_context); len_nc--; }

            // Remark: By property 2 of metavariable contexts, we
            // know that m can't occur in the reduced
            // nc.m_context.
            //
            // Property 2: If a metavariable ?m1 occurs in context ctx2 of
            // metavariable ?m2, then context ctx1 of ?m1 must be a prefix of ctx2.
            //

            // make sure nc that prefix of mc
            unify_ctx_prefix(nc.m_context, mc.m_context);

            fv_range = std::max(fv_range, len_nc);
        }
    };

    for_each_fn<decltype(proc)> visitor(proc);
    visitor(s);
    if (fv_range > length(mc.m_context)) {
        // s has a free variable that is not in the context of mc
        failed_to_unify();
    }
    mc.m_expr = s;
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

expr metavar_env::mk_metavar(context const & ctx) {
    m_modified    = true;
    unsigned vidx = m_cells.size();
    expr m = ::lean::mk_metavar(vidx);
    m_cells.push_back(cell(m, ctx, vidx));
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
            unsigned len_c = length(c.m_context);
            lean_assert(len_c <= ctx_size);
            if (len_c < ctx_size) {
                return lift_free_vars(c.m_expr, ctx_size - len_c);
            } else {
                return c.m_expr;
            }
        }
    } else {
        return e;
    }
}

void metavar_env::assign(expr const & m, expr const & s, context const & ctx) {
    lean_assert(is_metavar(m));
    lean_assert(!is_assigned(m));
    if (m == s)
        return;
    m_modified = true;
    cell & mc = root_cell(m);
    lean_assert(is_metavar(mc.m_expr));
    lean_assert(metavar_idx(mc.m_expr) == mc.m_find);
    expr _s = instantiate_metavars(s);
    if (is_metavar(_s)) {
        // both are unassigned meta-variables...
        lean_assert(!is_assigned(_s));
        cell & sc = root_cell(_s);
        lean_assert(is_metavar(sc.m_expr));
        ensure_same_length(mc.m_context, sc.m_context);
        unify_ctx_entries(mc.m_context, sc.m_context);
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
        assign_term(m, _s, ctx);
    }
    lean_assert(check_invariant());
}

expr metavar_env::instantiate_metavars(expr const & e) {
    auto it = [&](expr const & c, unsigned offset) -> expr {
        if (is_metavar(c)) {
            unsigned midx = metavar_idx(c);
            if (midx < m_cells.size()) {
                cell & rc = root_cell(midx);
                if (is_metavar(rc.m_expr)) {
                    return rc.m_expr;
                } else {
                    switch (rc.m_state) {
                    case state::Unprocessed: {
                        rc.m_state = state::Processing;
                        rc.m_expr  = instantiate_metavars(rc.m_expr);
                        rc.m_state = state::Processed;
                        lean_assert(length(rc.m_context) <= offset);
                        return lift_free_vars(rc.m_expr, offset - length(rc.m_context));
                    }
                    case state::Processing: throw exception("cycle detected");
                    case state::Processed:
                        lean_assert(length(rc.m_context) <= offset);
                        return lift_free_vars(rc.m_expr, offset - length(rc.m_context));
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

/**
   \brief Ensure both contexts have the same length
*/
void metavar_env::ensure_same_length(context & ctx1, context & ctx2) {
    if (is_eqp(ctx1, ctx2)) {
        return;
    } else {
        unsigned len1 = length(ctx1);
        unsigned len2 = length(ctx2);
        unsigned new_len = std::min(len1, len2);
        while (len1 > new_len) { ctx1 = cdr(ctx1); --len1; }
        while (len2 > new_len) { ctx2 = cdr(ctx2); --len2; }
    }
}

/**
   \brief Check if ctx1 is a prefix of ctx2. That is,
   1- length(ctx1) <= length(ctx2)
   2- Every entry in ctxt1 is unifiable with the corresponding
   entry in ctx2.
*/
void metavar_env::unify_ctx_prefix(context const & ctx1, context const & ctx2) {
    if (is_eqp(ctx1, ctx2)) {
        return;
    } else {
        unsigned len1 = length(ctx1);
        unsigned len2 = length(ctx2);
        if (len1 > len2)
            failed_to_unify();
        context _ctx2 = ctx2;
        while (len2 > len1) { _ctx2 = cdr(_ctx2); --len2; }
        unify_ctx_entries(ctx1, _ctx2);
    }
}

/**
   \brief Unify the context entries of the given contexts.

   \pre length(ctx1) == length(ctx2)
*/
void metavar_env::unify_ctx_entries(context const & ctx1, context const & ctx2) {
    lean_assert(length(ctx1) == length(ctx2));
    auto it1  = ctx1.begin();
    auto end1 = ctx1.end();
    auto it2  = ctx2.begin();
    for (; it1 != end1; ++it1, ++it2) {
        context_entry const & e1 = *it1;
        context_entry const & e2 = *it2;

        if ((e1.get_domain()) && (e2.get_domain())) {
            unify(e1.get_domain(), e2.get_domain());
        } else if (!(e1.get_domain()) && !(e2.get_domain())) {
            // do nothing
        } else {
            failed_to_unify();
        }

        if ((e1.get_body()) && (e2.get_body())) {
            unify(e1.get_body(), e2.get_body());
        } else if (!(e1.get_body()) && !(e2.get_body())) {
            // do nothing
        } else {
            failed_to_unify();
        }
    }
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
void metavar_env::unify_simple_ho_match(expr const & e1, expr const & e2, context const & ctx) {
    unify(arg(e1,0), mk_lambda(car(ctx).get_name(), car(ctx).get_domain(), e2), ctx);
}

/**
   \brief Auxiliary function for unifying expressions \c e1 and
   \c e2 when none of them are metavariables.
*/
void metavar_env::unify_core(expr const & e1, expr const & e2, context const & ctx) {
    check_interrupted(m_interrupted);
    lean_assert(!is_metavar(e1));
    lean_assert(!is_metavar(e2));
    if (e1 == e2) {
        return;
    } else if (is_type(e1) && is_type(e2)) {
        return; // ignoring type universe levels. We let the kernel check that
    } else if (is_abstraction(e1) && is_abstraction(e2)) {
        unify(abst_domain(e1), abst_domain(e2), ctx);
        unify(abst_body(e1),   abst_body(e2), extend(ctx, abst_name(e1), abst_domain(e1)));
    } else if (is_eq(e1) && is_eq(e2)) {
        unify(eq_lhs(e1), eq_lhs(e2), ctx);
        unify(eq_rhs(e1), eq_rhs(e2), ctx);
    } else {
        expr r1 = head_reduce(e1, m_env, m_available_definitions);
        expr r2 = head_reduce(e2, m_env, m_available_definitions);
        if (!is_eqp(e1, r1) || !is_eqp(e2, r2)) {
            return unify(r1, r2, ctx);
        } else if (is_app(e1) && is_app(e2) && num_args(e1) == num_args(e2)) {
            unsigned num = num_args(e1);
            for (unsigned i = 0; i < num; i++) {
                unify(arg(e1, i), arg(e2, i), ctx);
            }
        } else if (is_simple_ho_match(e1, e2, ctx)) {
            unify_simple_ho_match(e1, e2, ctx);
        } else if (is_simple_ho_match(e2, e1, ctx)) {
            unify_simple_ho_match(e2, e1, ctx);
        } else {
            failed_to_unify();
        }
    }
}

void metavar_env::unify(expr const & e1, expr const & e2, context const & ctx) {
    flet<unsigned> l(m_depth, m_depth+1);
    if (m_depth > m_max_depth)
        throw exception("unifier maximum recursion depth exceeded");
    expr const & r1 = root_at(e1, ctx);
    expr const & r2 = root_at(e2, ctx);
    if (is_metavar(r1)) {
        assign(r1, r2, ctx);
    } else {
        if (is_metavar(r2)) {
            assign(r2, r1, ctx);
        } else {
            unify_core(r1, r2, ctx);
        }
    }
}

context const & metavar_env::get_context(expr const & m) {
    lean_assert(is_metavar(m));
    return root_cell(m).m_context;
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
        if (c.m_context)
            out << ", " << c.m_context;
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

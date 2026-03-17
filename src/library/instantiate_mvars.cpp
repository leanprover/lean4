/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joachim Breitner
*/
#include <vector>
#include <unordered_map>
#include "util/name_set.h"
#include "util/name_hash_map.h"
#include "runtime/option_ref.h"
#include "runtime/array_ref.h"
#include "kernel/instantiate.h"
#include "kernel/expr.h"
#include "library/scope_cache.h"

/*
This module provides an implementation of `instantiateMVars` with linear
complexity in the presence of nested delayed-assigned metavariables and
improved sharing. It proceeds in two passes.

Terminology (for this file):

* Direct MVar: an MVar that is not delayed-assigned.
* Pending MVar: the direct MVar stored in a `DelayedMetavarAssignment`.
* Assigned MVar: a direct MVar with an assignment, or a delayed-assigned MVar
  with an assigned pending MVar.
* MVar DAG: the directed acyclic graph of MVars reachable from the expression.
* Resolvable MVar: an MVar where all MVars reachable from it (including itself)
  are assigned.
* Updateable MVar: an assigned direct MVar, or a delayed-assigned MVar that is
  resolvable but not reachable from any other resolvable delayed-assigned MVar.

In the MVar DAG, the updateable delayed-assigned MVars form a cut with only
assigned MVars behind it and no resolvable delayed-assigned MVars before it.

Pass 1 (`instantiate_direct_fn`):
  Traverses all MVars and expressions reachable from the initial expression and
  * instantiates all updateable direct MVars, updating their assignment with
    its instantiation,
  * instantiates all level MVars,
  * determines if there are any updateable delayed-assigned MVars.

Pass 2 (`instantiate_delayed_fn`):
  Only run if there are updateable delayed-assigned MVars. Has an "outer" and
  an "inner" mode, depending on whether it has crossed the updateable-MVar cut.

  In outer mode (empty substitution), all MVars are either unassigned direct
  MVars (left alone), non-updateable delayed-assigned MVars (pending MVar
  traversed in outer mode and updated with the result), or updateable
  delayed-assigned MVars.

  When a delayed-assigned MVar is encountered, its MVar DAG is explored (via
  `is_resolvable_pending`) to determine if it is resolvable (and thus
  updateable). Results are cached across invocations.

  If it is updateable, the substitution is initialized from its arguments and
  traversal continues with the value of its pending MVar in inner mode.

  In inner mode (non-empty substitution), all encountered delayed-assigned
  MVars are, by construction, resolvable but not updateable. The substitution
  is carried along and extended as we cross such MVars. Pending MVars of these
  delayed-assigned MVars are NOT updated with the result (as the result is
  valid only for this substitution, not in general).

  Applying the substitution in one go, rather than instantiating each
  delayed-assigned MVar on its own from inside out, avoids the quadratic
  overhead of that approach when there are long chains of delayed-assigned
  MVars.

  A special-crafted caching data structure, the `scope_cache`, ensures that
  sharing is preserved even across different delayed-assigned MVars (and hence
  with different substitutions), when possible.
*/

namespace lean {
extern "C" object * lean_get_lmvar_assignment(obj_arg mctx, obj_arg mid);
extern "C" object * lean_assign_lmvar(obj_arg mctx, obj_arg mid, obj_arg val);
extern "C" object * lean_get_mvar_assignment(obj_arg mctx, obj_arg mid);
extern "C" object * lean_get_delayed_mvar_assignment(obj_arg mctx, obj_arg mid);
extern "C" object * lean_delayed_mvar_assignment_fvars(obj_arg d);
extern "C" object * lean_delayed_mvar_assignment_mvar_id_pending(obj_arg d);
extern "C" object * lean_assign_mvar(obj_arg mctx, obj_arg mid, obj_arg val);
typedef object_ref metavar_ctx;
typedef object_ref delayed_assignment;

static void assign_lmvar(metavar_ctx & mctx, name const & mid, level const & l) {
    object * r = lean_assign_lmvar(mctx.steal(), mid.to_obj_arg(), l.to_obj_arg());
    mctx.set_box(r);
}

static option_ref<level> get_lmvar_assignment(metavar_ctx & mctx, name const & mid) {
    return option_ref<level>(lean_get_lmvar_assignment(mctx.to_obj_arg(), mid.to_obj_arg()));
}

static void assign_mvar(metavar_ctx & mctx, name const & mid, expr const & e) {
    object * r = lean_assign_mvar(mctx.steal(), mid.to_obj_arg(), e.to_obj_arg());
    mctx.set_box(r);
}

static option_ref<expr> get_mvar_assignment(metavar_ctx & mctx, name const & mid) {
    return option_ref<expr>(lean_get_mvar_assignment(mctx.to_obj_arg(), mid.to_obj_arg()));
}

static option_ref<delayed_assignment> get_delayed_mvar_assignment(metavar_ctx & mctx, name const & mid) {
    return option_ref<delayed_assignment>(lean_get_delayed_mvar_assignment(mctx.to_obj_arg(), mid.to_obj_arg()));
}

static array_ref<expr> delayed_assignment_fvars(delayed_assignment const & d) {
    return array_ref<expr>(lean_delayed_mvar_assignment_fvars(d.to_obj_arg()));
}

static name delayed_assignment_mvar_id_pending(delayed_assignment const & d) {
    return name(lean_delayed_mvar_assignment_mvar_id_pending(d.to_obj_arg()));
}

/* Level metavariable instantiation. */
class instantiate_lmvars_all_fn {
    metavar_ctx & m_mctx;
    lean::unordered_map<lean_object *, level> m_cache;
    std::vector<level> m_saved;

    inline level cache(level const & l, level r, bool shared) {
        if (shared) {
            m_cache.insert(mk_pair(l.raw(), r));
        }
        return r;
    }
public:
    instantiate_lmvars_all_fn(metavar_ctx & mctx):m_mctx(mctx) {}
    level visit(level const & l) {
        if (!has_mvar(l))
            return l;
        bool shared = false;
        if (is_shared(l)) {
            auto it = m_cache.find(l.raw());
            if (it != m_cache.end()) {
                return it->second;
            }
            shared = true;
        }
        switch (l.kind()) {
        case level_kind::Succ:
            return cache(l, update_succ(l, visit(succ_of(l))), shared);
        case level_kind::Max: case level_kind::IMax:
            return cache(l, update_max(l, visit(level_lhs(l)), visit(level_rhs(l))), shared);
        case level_kind::Zero: case level_kind::Param:
            lean_unreachable();
        case level_kind::MVar: {
            option_ref<level> r = get_lmvar_assignment(m_mctx, mvar_id(l));
            if (!r) {
                return l;
            } else {
                level a(r.get_val());
                if (!has_mvar(a)) {
                    return a;
                } else {
                    level a_new = visit(a);
                    if (!is_eqp(a, a_new)) {
                        m_saved.push_back(a);
                        assign_lmvar(m_mctx, mvar_id(l), a_new);
                    }
                    return a_new;
                }
            }
        }}
    }
    level operator()(level const & l) { return visit(l); }
};

/* ============================================================================
   Pass 1: Instantiate updateable direct MVars with write-back.
   For delayed-assigned MVars, pre-normalize the pending MVar's value
   (resolving its direct MVar chains) but leave the delayed-assigned MVar
   application in the expression. Also instantiates level MVars.
   Unassigned MVars are left in place.
   ============================================================================ */

class instantiate_direct_fn {
    metavar_ctx & m_mctx;
    instantiate_lmvars_all_fn m_level_fn;
    name_set m_already_normalized;
    /* Set to true when a delayed-assigned MVar with an assigned pending MVar
       is encountered. Pass 2 is needed to resolve or write back such MVars. */
    bool m_has_updateable_delayed;

    lean::unordered_map<lean_object *, expr> m_cache;
    std::vector<expr> m_saved;

    level visit_level(level const & l) {
        return m_level_fn(l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls, [&](level const & l) { return visit_level(l); });
    }

    inline expr cache(expr const & e, expr r, bool shared) {
        if (shared) {
            m_cache.insert(mk_pair(e.raw(), r));
        }
        return r;
    }

    /* Get and normalize an updateable direct MVar's assignment. Write back the
       normalized value. */
    optional<expr> get_assignment(name const & mid) {
        option_ref<expr> r = get_mvar_assignment(m_mctx, mid);
        if (!r) {
            return optional<expr>();
        }
        expr a(r.get_val());
        if (!has_mvar(a) || m_already_normalized.contains(mid)) {
            return optional<expr>(a);
        }
        m_already_normalized.insert(mid);
        expr a_new = visit(a);
        if (!is_eqp(a, a_new)) {
            m_saved.push_back(a);
            assign_mvar(m_mctx, mid, a_new);
        }
        return optional<expr>(a_new);
    }

    /* Visit an application whose head is not an MVar, preserving sharing of
       application prefixes (e.g. for `f a b c`, if only `c` changes,
       the nodes `f a` and `f a b` are pointer-shared with the original). */
    expr visit_nonmvar_app(expr const & e) {
        expr new_a = visit(app_arg(e));
        expr const & fn = app_fn(e);
        expr new_f = is_app(fn) ? visit_nonmvar_app(fn) : visit(fn);
        return update_app(e, new_f, new_a);
    }

    /* Collect the application spine into a buffer and apply beta reduction. */
    expr visit_app_beta(expr const & f_new, expr const & e) {
        buffer<expr> args;
        expr const * curr = &e;
        while (is_app(*curr)) {
            args.push_back(visit(app_arg(*curr)));
            curr = &app_fn(*curr);
        }
        bool preserve_data = false;
        bool zeta = true;
        return apply_beta(f_new, args.size(), args.data(), preserve_data, zeta);
    }

    expr visit_app(expr const & e) {
        expr const & f = get_app_fn(e);
        if (!is_mvar(f)) {
            return visit_nonmvar_app(e);
        }
        name const & mid = mvar_name(f);
        /* Direct MVar assignment takes precedence. */
        if (auto f_new = get_assignment(mid)) {
            return visit_app_beta(*f_new, e);
        }
        /* Check for delayed-assigned MVar. */
        option_ref<delayed_assignment> d = get_delayed_mvar_assignment(m_mctx, mid);
        if (d) {
            /* Pre-normalize the pending MVar's value so pass 2 finds it ready.
               Only trigger pass 2 if the pending MVar is actually assigned;
               unassigned pending MVars will clearly fail the resolvability check. */
            name mid_pending = delayed_assignment_mvar_id_pending(d.get_val());
            if (get_assignment(mid_pending))
                m_has_updateable_delayed = true;
        }
        /* Unresolved MVar head: visit structurally, preserving app prefix sharing. */
        return visit_nonmvar_app(e);
    }

    expr visit_mvar(expr const & e) {
        name const & mid = mvar_name(e);
        if (auto r = get_assignment(mid)) {
            return *r;
        }
        /* Not a direct MVar with assignment. Check if delayed-assigned. */
        option_ref<delayed_assignment> d = get_delayed_mvar_assignment(m_mctx, mid);
        if (d) {
            name mid_pending = delayed_assignment_mvar_id_pending(d.get_val());
            if (get_assignment(mid_pending))
                m_has_updateable_delayed = true;
        }
        return e;
    }

public:
    instantiate_direct_fn(metavar_ctx & mctx)
        : m_mctx(mctx), m_level_fn(mctx), m_has_updateable_delayed(false) {}
    bool has_updateable_delayed() const { return m_has_updateable_delayed; }

    expr visit(expr const & e) {
        if (!has_mvar(e))
            return e;
        bool shared = false;
        if (is_shared(e)) {
            auto it = m_cache.find(e.raw());
            if (it != m_cache.end()) {
                return it->second;
            }
            shared = true;
        }

        switch (e.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:  case expr_kind::FVar:
            lean_unreachable();
        case expr_kind::Sort:
            return cache(e, update_sort(e, visit_level(sort_level(e))), shared);
        case expr_kind::Const:
            return cache(e, update_const(e, visit_levels(const_levels(e))), shared);
        case expr_kind::MVar:
            return visit_mvar(e);
        case expr_kind::MData:
            return cache(e, update_mdata(e, visit(mdata_expr(e))), shared);
        case expr_kind::Proj:
            return cache(e, update_proj(e, visit(proj_expr(e))), shared);
        case expr_kind::App:
            return cache(e, visit_app(e), shared);
        case expr_kind::Pi: case expr_kind::Lambda:
            return cache(e, update_binding(e, visit(binding_domain(e)), visit(binding_body(e))), shared);
        case expr_kind::Let:
            return cache(e, update_let(e, visit(let_type(e)), visit(let_value(e)), visit(let_body(e))), shared);
        }
    }

    expr operator()(expr const & e) { return visit(e); }
};

/* ============================================================================
   Pass 2: Resolve delayed-assigned MVars with fused fvar substitution.
   Direct MVar chains have been pre-resolved by pass 1.

   Write-back behavior:

   Delayed-assigned MVars form a dependency tree: each delayed-assigned MVar's
   pending MVar value may reference other delayed-assigned MVars. Some subtrees
   of this tree are fully resolvable (all delayed-assigned MVars within are
   resolvable), while others are not.

   Pass 2 fully resolves every maximal resolvable subtree. The roots of these
   subtrees — updateable delayed-assigned MVars that are resolvable but whose
   parent in the tree is not — form the updateable-MVar cut through the
   dependency tree. Above the cut sit non-resolvable delayed-assigned MVars;
   below the cut, everything is resolved.

   Pass 2 writes back the normalized pending MVar values of delayed-assigned
   MVars above the cut (the non-resolvable ones whose children may have been
   resolved). This is exactly the right set: these MVars are visited in outer
   mode (empty fvar substitution), so their normalized values are suitable for
   storing in the mctx. MVars below the cut are visited in inner mode
   (non-empty substitution, fvars replaced by arguments), so their intermediate
   values cannot be written back.
   ============================================================================ */

struct fvar_subst_entry {
    unsigned depth;
    unsigned scope;
    expr     value;
};

class instantiate_delayed_fn {
    metavar_ctx & m_mctx;
    name_hash_map<fvar_subst_entry> m_fvar_subst;
    unsigned m_depth;

    /* Scope-aware cache for (ptr, depth) → expr with lazy staleness detection. */
    struct key_hasher {
        std::size_t operator()(std::pair<lean_object *, unsigned> const & p) const {
            return hash((size_t)p.first >> 3, p.second);
        }
    };
    typedef std::pair<lean_object *, unsigned> cache_key;
    scope_cache<cache_key, expr, key_hasher> m_cache;

    /* After visit() returns, this holds the maximum fvar-substitution
       scope that contributed to the result — i.e., the outermost scope at which the
       result is valid and can be cached. Updated monotonically (via max) through
       the save/reset/restore pattern in visit(). */
    unsigned m_result_scope;

    /* Write-back support: in outer mode, normalize and write back direct MVar
       assignments. Downstream code (e.g. MutualDef.mkInitialUsedFVarsMap) reads
       stored assignments and expects inner delayed-assigned MVars to be resolved. */
    name_set m_already_normalized;
    std::vector<expr> m_saved;

    /* Resolvability caches — persistent across all delayed-assigned MVar
       resolutions. A pending MVar is resolvable if its assigned value
       (normalized by pass 1) would become MVar-free after resolution: all
       remaining MVars must be delayed-assigned MVars in app position with
       enough arguments, whose own pending MVars are also resolvable. */
    lean::unordered_map<lean_object *, bool> m_resolvable_expr_cache;
    name_hash_map<unsigned> m_resolvable_pending_cache; /* 0 = in-progress, 1 = yes, 2 = no */

    bool is_resolvable_pending(name const & pending) {
        auto it = m_resolvable_pending_cache.find(pending);
        if (it != m_resolvable_pending_cache.end())
            return it->second == 1;
        /* Mark in-progress (cycle guard — shouldn't happen). */
        m_resolvable_pending_cache[pending] = 0;
        option_ref<expr> r = get_mvar_assignment(m_mctx, pending);
        if (!r) {
            m_resolvable_pending_cache[pending] = 2;
            return false;
        }
        bool ok = is_resolvable_expr(expr(r.get_val()));
        m_resolvable_pending_cache[pending] = ok ? 1 : 2;
        return ok;
    }

    bool is_resolvable_expr(expr const & e) {
        if (!has_expr_mvar(e)) return true;
        if (is_shared(e)) {
            auto it = m_resolvable_expr_cache.find(e.raw());
            if (it != m_resolvable_expr_cache.end())
                return it->second;
        }
        bool r = is_resolvable_expr_core(e);
        if (is_shared(e))
            m_resolvable_expr_cache[e.raw()] = r;
        return r;
    }

    bool is_resolvable_expr_core(expr const & e) {
        switch (e.kind()) {
        case expr_kind::MVar:
            /* Bare MVar — direct MVar assignments were resolved by pass 1. Stuck. */
            return false;
        case expr_kind::App: {
            expr const & f = get_app_fn(e);
            if (is_mvar(f)) {
                name const & mid = mvar_name(f);
                option_ref<delayed_assignment> d =
                    get_delayed_mvar_assignment(m_mctx, mid);
                if (!d) return false;
                array_ref<expr> fvars = delayed_assignment_fvars(d.get_val());
                if (fvars.size() > get_app_num_args(e))
                    return false; /* not enough args */
                name mid_pending = delayed_assignment_mvar_id_pending(d.get_val());
                if (!is_resolvable_pending(mid_pending))
                    return false;
                /* Check args too. */
                expr const * curr = &e;
                while (is_app(*curr)) {
                    if (!is_resolvable_expr(app_arg(*curr)))
                        return false;
                    curr = &app_fn(*curr);
                }
                return true;
            }
            return is_resolvable_expr(app_fn(e)) && is_resolvable_expr(app_arg(e));
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            return is_resolvable_expr(binding_domain(e)) &&
                   is_resolvable_expr(binding_body(e));
        case expr_kind::Let:
            return is_resolvable_expr(let_type(e)) &&
                   is_resolvable_expr(let_value(e)) &&
                   is_resolvable_expr(let_body(e));
        case expr_kind::MData:
            return is_resolvable_expr(mdata_expr(e));
        case expr_kind::Proj:
            return is_resolvable_expr(proj_expr(e));
        default:
            return true;
        }
    }

    /* Outer mode: no fvar substitution active; inner mode: inside a
       resolvable delayed-assigned MVar with fvars mapped to arguments. */
    bool in_outer_mode() const {
        return m_fvar_subst.empty();
    }

    optional<expr> lookup_fvar(name const & fid) {
        auto it = m_fvar_subst.find(fid);
        if (it == m_fvar_subst.end())
            return optional<expr>();
        m_result_scope = std::max(m_result_scope, it->second.scope);
        unsigned d = m_depth - it->second.depth;
        if (d == 0)
            return optional<expr>(it->second.value);
        return optional<expr>(lift_loose_bvars(it->second.value, d));
    }

    /* Get a direct MVar assignment. Visit it to resolve delayed-assigned
       MVars and apply the fvar substitution.
       In outer mode, normalize and write back the result to the mctx.
       Downstream code (e.g. MutualDef.mkInitialUsedFVarsMap) reads stored
       assignments and expects inner delayed-assigned MVars to be resolved.
       In inner mode, no write-back: the result contains fvar-substituted
       terms not suitable for the mctx. */
    optional<expr> get_assignment(name const & mid) {
        option_ref<expr> r = get_mvar_assignment(m_mctx, mid);
        if (!r)
            return optional<expr>();
        expr a(r.get_val());
        if (in_outer_mode()) {
            if (m_already_normalized.contains(mid))
                return optional<expr>(a);
            m_already_normalized.insert(mid);
            expr a_new = visit(a);
            if (!is_eqp(a, a_new)) {
                m_saved.push_back(a);
                assign_mvar(m_mctx, mid, a_new);
            }
            return optional<expr>(a_new);
        } else {
            return optional<expr>(visit(a));
        }
    }

    expr visit_delayed(array_ref<expr> const & fvars, name const & mid_pending,
                       expr const & e) {
        buffer<expr> args;
        expr const * curr = &e;
        while (is_app(*curr)) {
            args.push_back(visit(app_arg(*curr)));
            curr = &app_fn(*curr);
        }

        size_t fvar_count = fvars.size();
        size_t extra_count = args.size() - fvar_count;

        /* Push a new scope and extend the fvar substitution. */
        m_cache.push();
        struct saved_entry { name key; bool had_old; fvar_subst_entry old; };
        std::vector<saved_entry> saved_entries;
        saved_entries.reserve(fvar_count);
        for (size_t i = 0; i < fvar_count; i++) {
            name const & fid = fvar_name(fvars[i]);
            auto old_it = m_fvar_subst.find(fid);
            if (old_it != m_fvar_subst.end()) {
                saved_entries.push_back({fid, true, old_it->second});
            } else {
                saved_entries.push_back({fid, false, {0, 0, expr()}});
            }
            m_fvar_subst[fid] = {m_depth, m_cache.scope(), args[args.size() - 1 - i]};
        }

        /* Get the pending MVar's value directly — it must be assigned (pass 1
           pre-normalized it). No write-back: we are in inner mode. */
        option_ref<expr> pending_val = get_mvar_assignment(m_mctx, mid_pending);
        lean_assert(!!pending_val);
        expr val_new = visit(expr(pending_val.get_val()));

        /* Pop scope; stale entries are detected by generation mismatch on lookup. */
        m_cache.pop();

        /* The result no longer depends on the popped scope — all fvars from
           that scope have been substituted. Clamp result_scope to the current
           scope so that cache entries for this result (and ancestors) are not
           spuriously invalidated. Dependencies on outer scopes (from fvars of
           enclosing delayed MVars) are preserved since they are ≤ m_scope. */
        m_result_scope = std::min(m_result_scope, m_cache.scope());

        /* Restore the fvar substitution. */
        for (auto & se : saved_entries) {
            if (!se.had_old) {
                m_fvar_subst.erase(se.key);
            } else {
                m_fvar_subst[se.key] = se.old;
            }
        }

        /* Use apply_beta instead of mk_rev_app: pass 1's beta-reduction may have
           changed delayed-assigned MVar arguments (e.g., substituting a bvar with a
           concrete value), so the resolved pending MVar value may be a lambda that
           needs beta-reduction with the extra args. */
        bool preserve_data = false;
        bool zeta = true;
        return apply_beta(val_new, extra_count, args.data(), preserve_data, zeta);
    }

    /* Visit an application whose head is not an MVar, preserving sharing of
       application prefixes. */
    expr visit_nonmvar_app(expr const & e) {
        expr new_a = visit(app_arg(e));
        expr const & fn = app_fn(e);
        expr new_f = is_app(fn) ? visit_nonmvar_app(fn) : visit(fn);
        return update_app(e, new_f, new_a);
    }

    expr visit_app(expr const & e) {
        expr const & f = get_app_fn(e);
        if (!is_mvar(f)) {
            return visit_nonmvar_app(e);
        }
        name const & mid = mvar_name(f);
        /* Direct MVar assignments were resolved by pass 1. */
        lean_assert(!get_mvar_assignment(m_mctx, mid));
        /* Check for delayed-assigned MVar. */
        option_ref<delayed_assignment> d = get_delayed_mvar_assignment(m_mctx, mid);
        if (!d) {
            return visit_nonmvar_app(e);
        }
        array_ref<expr> fvars = delayed_assignment_fvars(d.get_val());
        name mid_pending = delayed_assignment_mvar_id_pending(d.get_val());
        if (fvars.size() > get_app_num_args(e)) {
            return visit_nonmvar_app(e);
        }
        if (is_resolvable_pending(mid_pending)) {
            /* Updateable delayed-assigned MVar: cross the cut into inner mode. */
            return visit_delayed(fvars, mid_pending, e);
        } else {
            /* Non-resolvable delayed-assigned MVars only appear in outer mode:
               inside a resolvable subtree all nested delayed-assigned MVars are
               resolvable too. */
            lean_assert(in_outer_mode());
            /* Normalize the pending MVar's value for mctx write-back
               (see write-back comment above). */
            (void)get_assignment(mid_pending);
            return visit_nonmvar_app(e);
        }
    }

    expr visit_fvar(expr const & e) {
        name const & fid = fvar_name(e);
        if (auto r = lookup_fvar(fid)) {
            return *r;
        }
        return e;
    }

public:
    instantiate_delayed_fn(metavar_ctx & mctx)
        : m_mctx(mctx), m_depth(0), m_result_scope(0) {}

    expr visit(expr const & e) {
        if ((!has_fvar(e) || in_outer_mode()) && !has_expr_mvar(e))
            return e;

        bool shared = false;
        if (is_shared(e)) {
            if (auto r = m_cache.lookup(cache_key(e.raw(), m_depth), m_result_scope))
                return *r;
            shared = true;
        }

        /* Save and reset the result scope for this subtree.
           After computing, cache_insert uses m_result_scope to place the entry
           at the outermost valid scope level. Then we restore the parent's
           watermark, taking the max with our contribution. */
        unsigned saved_result_scope = m_result_scope;
        m_result_scope = 0;

        expr r;
        switch (e.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:
            lean_unreachable();
        case expr_kind::FVar:
            r = visit_fvar(e);
            goto done; /* skip caching for fvars */
        case expr_kind::Sort:
        case expr_kind::Const:
            /* Sorts and Consts have no fvars and no expr MVars (level MVars
               were resolved by pass 1), so the early exit above catches them. */
            lean_unreachable();
        case expr_kind::MVar:
            /* Bare MVars in pass 2 are unassigned direct MVars: direct MVar
               assignments were resolved by pass 1, and resolvable pending MVar
               values contain no bare unassigned MVars. They only appear in
               outer mode (at the top level or during write-back normalization). */
            lean_assert(in_outer_mode());
            lean_assert(!get_mvar_assignment(m_mctx, mvar_name(e)));
            r = e;
            goto done;
        case expr_kind::MData:
            r = update_mdata(e, visit(mdata_expr(e)));
            break;
        case expr_kind::Proj:
            r = update_proj(e, visit(proj_expr(e)));
            break;
        case expr_kind::App:
            r = visit_app(e);
            break;
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr d = visit(binding_domain(e));
            m_depth++;
            expr b = visit(binding_body(e));
            m_depth--;
            r = update_binding(e, d, b);
            break;
        }
        case expr_kind::Let: {
            expr t = visit(let_type(e));
            expr v = visit(let_value(e));
            m_depth++;
            expr b = visit(let_body(e));
            m_depth--;
            r = update_let(e, t, v, b);
            break;
        }
        }
        if (shared) {
            r = m_cache.insert(cache_key(e.raw(), m_depth), r, m_result_scope);
        }

    done:
        m_result_scope = std::max(saved_result_scope, m_result_scope);
        return r;
    }

    expr operator()(expr const & e) { return visit(e); }
};

/* ============================================================================
   Entry points: run pass 1 then pass 2.
   ============================================================================ */

static object * run_instantiate_all(object * m, object * e) {
    metavar_ctx mctx(m);

    /* Pass 1: instantiate updateable direct MVars, pre-normalize pending MVar values. */
    instantiate_direct_fn pass1(mctx);
    expr e1 = pass1(expr(e));

    /* Pass 2: resolve delayed-assigned MVars with fused fvar substitution.
       Skip if pass 1 found no delayed-assigned MVars with assigned pending
       MVars — none need resolution or write-back. */
    expr e2;
    if (!pass1.has_updateable_delayed()) {
        e2 = e1;
    } else {
        instantiate_delayed_fn pass2(mctx);
        e2 = pass2(e1);
    }

    /* (mctx, expr) */
    object * r = alloc_cnstr(0, 2, 0);
    cnstr_set(r, 0, mctx.steal());
    cnstr_set(r, 1, e2.steal());
    return r;
}

extern "C" LEAN_EXPORT object * lean_instantiate_level_mvars(object * m, object * l) {
    metavar_ctx mctx(m);
    level l_new = instantiate_lmvars_all_fn(mctx)(level(l));
    object * r = alloc_cnstr(0, 2, 0);
    cnstr_set(r, 0, mctx.steal());
    cnstr_set(r, 1, l_new.steal());
    return r;
}

extern "C" LEAN_EXPORT object * lean_instantiate_expr_mvars(object * m, object * e) {
    return run_instantiate_all(m, e);
}
}

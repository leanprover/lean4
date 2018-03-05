/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/scoped_map.h"
#include "util/name_map.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/idx_metavar.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/cache_helper.h"
#include "library/app_builder.h"
#include "library/relation_manager.h"

namespace lean {
static void trace_fun(name const & n) {
    tout() << "failed to create an '" << n << "'-application";
}

static void trace_failure(name const & n, unsigned nargs, char const * msg) {
    lean_trace("app_builder",
               trace_fun(n); tout() << " with " << nargs << ", " << msg << "\n";);
}

static void trace_failure(name const & n, char const * msg) {
    lean_trace("app_builder",
               trace_fun(n); tout() << ", " << msg << "\n";);
}

#define lean_app_builder_trace_core(ctx, code) lean_trace("app_builder", scope_trace_env _scope1(ctx.env(), ctx); code)
#define lean_app_builder_trace(code) lean_app_builder_trace_core(m_ctx, code)

static unsigned get_nargs(unsigned mask_sz, bool const * mask) {
    unsigned nargs = 0;
    for (unsigned i = 0; i < mask_sz; i++) {
        if (mask[i])
            nargs++;
    }
    return nargs;
}

class app_builder_cache {
    struct entry {
        unsigned             m_num_umeta;
        unsigned             m_num_emeta;
        expr                 m_app;
        list<optional<expr>> m_inst_args; // "mask" of implicit instance arguments
        list<expr>           m_expl_args; // metavars for explicit arguments
        /*
          IMPORTANT: for m_inst_args we store the arguments in reverse order.
          For example, the first element in the list indicates whether the last argument
          is an instance implicit argument or not. If it is not none, then the element
          is the associated metavariable

          m_expl_args are also stored in reverse order
        */
    };

    struct key {
        name       m_name;
        unsigned   m_num_expl;
        unsigned   m_hash;
        // If nil, then the mask is composed of the last m_num_expl arguments.
        // If nonnil, then the mask is NOT of the form [false*, true*]
        list<bool> m_mask;

        key(name const & c, unsigned n):
            m_name(c), m_num_expl(n),
            m_hash(::lean::hash(c.hash(), n)) {
        }

        key(name const & c, list<bool> const & m):
            m_name(c), m_num_expl(length(m)) {
            m_hash = ::lean::hash(c.hash(), m_num_expl);
            m_mask = m;
            for (bool b : m) {
                if (b)
                    m_hash = ::lean::hash(m_hash, 17u);
                else
                    m_hash = ::lean::hash(m_hash, 31u);
            }
        }

        bool check_invariant() const {
            lean_assert(empty(m_mask) || length(m_mask) == m_num_expl);
            return true;
        }

        unsigned hash() const { return m_hash; }
        friend bool operator==(key const & k1, key const & k2) {
            return k1.m_name == k2.m_name && k1.m_num_expl == k2.m_num_expl && k1.m_mask == k2.m_mask;
        }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.hash(); }
    };

    typedef std::unordered_map<key, entry, key_hash_fn> map;

    environment          m_env;
    map                  m_map;
    friend class app_builder;
public:
    app_builder_cache(environment const & env):
        m_env(env) {
    }

    environment const & env() const { return m_env; }
};

typedef cache_compatibility_helper<app_builder_cache> app_builder_cache_helper;

/* CACHE_RESET: YES */
MK_THREAD_LOCAL_GET_DEF(app_builder_cache_helper, get_abch);

/** Return an app_builder_cache for the transparency_mode in ctx, and compatible with the environment. */
app_builder_cache & get_app_builder_cache_for(type_context_old const & ctx) {
    return get_abch().get_cache_for(ctx);
}

static level get_level_ap(type_context_old & ctx, expr const & A) {
    try {
        return get_level(ctx, A);
    } catch (exception &) {
        lean_app_builder_trace_core(ctx, tout() << "failed to infer universe level for type " << A << "\n";);
        throw app_builder_exception();
    }
}

/** \brief Helper for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
        rel.{l_1 l_2} : Pi (A : Type.{l_1}) (B : A -> Type.{l_2}), (Pi x : A, B x) -> (Pi x : A, B x) -> , Prop
        nat     : Type.{1}
        real    : Type.{1}
        vec.{l} : Pi (A : Type.{l}) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    then
        builder.mk_app(rel, f, g)
    returns the application
        rel.{1 2} nat (fun n : nat, vec real n) f g
*/
class app_builder {
    type_context_old &      m_ctx;
    app_builder_cache & m_cache;
    typedef app_builder_cache::key   key;
    typedef app_builder_cache::entry entry;

    environment const & env() const { return m_ctx.env(); }

    levels mk_metavars(declaration const & d, buffer<expr> & mvars, buffer<optional<expr>> & inst_args) {
        unsigned num_univ = d.get_num_univ_params();
        buffer<level> lvls_buffer;
        for (unsigned i = 0; i < num_univ; i++) {
            lvls_buffer.push_back(m_ctx.mk_tmp_univ_mvar());
        }
        levels lvls = to_list(lvls_buffer);
        expr type   = m_ctx.relaxed_whnf(instantiate_type_univ_params(d, lvls));
        while (is_pi(type)) {
            expr mvar = m_ctx.mk_tmp_mvar(binding_domain(type));
            if (binding_info(type).is_inst_implicit())
                inst_args.push_back(some_expr(mvar));
            else
                inst_args.push_back(none_expr());
            mvars.push_back(mvar);
            type = m_ctx.relaxed_whnf(instantiate(binding_body(type), mvar));
        }
        return lvls;
    }

    optional<entry> get_entry(name const & c, unsigned nargs) {
        key k(c, nargs);
        lean_assert(k.check_invariant());
        auto it = m_cache.m_map.find(k);
        if (it == m_cache.m_map.end()) {
            if (auto d = env().find(c)) {
                buffer<expr> mvars;
                buffer<optional<expr>> inst_args;
                levels lvls = mk_metavars(*d, mvars, inst_args);
                if (nargs > mvars.size())
                    return optional<entry>(); // insufficient number of arguments
                entry e;
                e.m_num_umeta = d->get_num_univ_params();
                e.m_num_emeta = mvars.size();
                e.m_app       = ::lean::mk_app(mk_constant(c, lvls), mvars);
                e.m_inst_args = reverse_to_list(inst_args.begin(), inst_args.end());
                e.m_expl_args = reverse_to_list(mvars.begin() + mvars.size() - nargs, mvars.end());
                m_cache.m_map.insert(mk_pair(k, e));
                return optional<entry>(e);
            } else {
                return optional<entry>(); // unknown decl
            }
        } else {
            return optional<entry>(it->second);
        }
    }

    levels mk_metavars(declaration const & d, unsigned arity, buffer<expr> & mvars, buffer<optional<expr>> & inst_args) {
        unsigned num_univ = d.get_num_univ_params();
        buffer<level> lvls_buffer;
        for (unsigned i = 0; i < num_univ; i++) {
            lvls_buffer.push_back(m_ctx.mk_tmp_univ_mvar());
        }
        levels lvls = to_list(lvls_buffer);
        expr type   = instantiate_type_univ_params(d, lvls);
        for (unsigned i = 0; i < arity; i++) {
            type   = m_ctx.relaxed_whnf(type);
            if (!is_pi(type)) {
                trace_failure(d.get_name(), arity, "too many arguments");
                throw app_builder_exception();
            }
            expr mvar = m_ctx.mk_tmp_mvar(binding_domain(type));
            if (binding_info(type).is_inst_implicit())
                inst_args.push_back(some_expr(mvar));
            else
                inst_args.push_back(none_expr());
            mvars.push_back(mvar);
            type = instantiate(binding_body(type), mvar);
        }
        return lvls;
    }

    optional<entry> get_entry(name const & c, unsigned mask_sz, bool const * mask) {
        key k(c, to_list(mask, mask+mask_sz));
        lean_assert(k.check_invariant());
        auto it = m_cache.m_map.find(k);
        if (it == m_cache.m_map.end()) {
            if (auto d = env().find(c)) {
                buffer<expr> mvars;
                buffer<optional<expr>> inst_args;
                levels lvls = mk_metavars(*d, mask_sz, mvars, inst_args);
                entry e;
                e.m_num_umeta = d->get_num_univ_params();
                e.m_num_emeta = mvars.size();
                e.m_app       = ::lean::mk_app(mk_constant(c, lvls), mvars);
                e.m_inst_args = reverse_to_list(inst_args.begin(), inst_args.end());
                list<expr> expl_args;
                for (unsigned i = 0; i < mask_sz; i++) {
                    if (mask[i])
                        expl_args = cons(mvars[i], expl_args);
                }
                e.m_expl_args = expl_args;
                m_cache.m_map.insert(mk_pair(k, e));
                return optional<entry>(e);
            } else {
                return optional<entry>(); // unknown decl
            }
        } else {
            return optional<entry>(it->second);
        }
    }

    bool check_all_assigned(entry const & e) {
        lean_assert(e.m_num_emeta == length(e.m_inst_args));
        // recall that the flags at e.m_inst_args are stored in reverse order.
        // For example, the first flag in the list indicates whether the last argument
        // is an instance implicit argument or not.
        unsigned i = e.m_num_emeta;
        for (optional<expr> const & inst_arg : e.m_inst_args) {
            lean_assert(i > 0);
            --i;
            if (!m_ctx.get_tmp_mvar_assignment(i)) {
                if (inst_arg) {
                    expr type = m_ctx.instantiate_mvars(mlocal_type(*inst_arg));
                    if (auto v = m_ctx.mk_class_instance(type)) {
                        if (!m_ctx.is_def_eq(*inst_arg, *v)) {
                            // failed to assign instance
                            return false;
                        }
                    } else {
                        // failed to generate instance
                        return false;
                    }
                } else {
                    // unassined metavar
                    return false;
                }
            }
        }
        for (unsigned i = 0; i < e.m_num_umeta; i++) {
            if (!m_ctx.get_tmp_uvar_assignment(i))
                return false;
        }
        return true;
    }

    void init_ctx_for(entry const & e) {
        m_ctx.ensure_num_tmp_mvars(e.m_num_umeta, e.m_num_emeta);
    }

    void trace_unify_failure(name const & n, unsigned i, expr const & m, expr const & v) {
        lean_app_builder_trace(
            trace_fun(n);
            tout () << ", failed to solve unification constraint for #" << (i+1)
            << " argument (" << m_ctx.instantiate_mvars(m_ctx.infer(m)) << " =?= "
            << m_ctx.instantiate_mvars(m_ctx.infer(v)) << ")\n";);
    }

    void trace_inst_failure(expr const & A, char const * n) {
        lean_app_builder_trace(tout() << "failed to build instance of '" << n << "' for " << A << "\n";);
    }

public:
    app_builder(type_context_old & ctx):m_ctx(ctx), m_cache(get_app_builder_cache_for(ctx)) {}

    level get_level(expr const & A) {
        return get_level_ap(m_ctx, A);
    }

    expr mk_app(name const & c, unsigned nargs, expr const * args) {
        lean_assert(std::all_of(args, args + nargs, [](expr const & arg) { return !has_idx_metavar(arg); }))
        type_context_old::tmp_mode_scope scope(m_ctx);
        optional<entry> e = get_entry(c, nargs);
        if (!e) {
            trace_failure(c, "failed to retrieve declaration");
            throw app_builder_exception();
        }
        init_ctx_for(*e);
        unsigned i = nargs;
        for (auto m : e->m_expl_args) {
            if (i == 0) {
                trace_failure(c, "too many explicit arguments");
                throw app_builder_exception();
            }
            --i;
            if (!m_ctx.is_def_eq(m, args[i])) {
                trace_unify_failure(c, i, m, args[i]);
                throw app_builder_exception();
            }
        }
        if (!check_all_assigned(*e)) {
            trace_failure(c, "there are missing implicit arguments");
            throw app_builder_exception();
        }
        return m_ctx.instantiate_mvars(e->m_app);
    }

    expr mk_app(name const & c, std::initializer_list<expr> const & args) {
        return mk_app(c, args.size(), args.begin());
    }

    expr mk_app(name const & c, expr const & a1) {
        return mk_app(c, {a1});
    }

    expr mk_app(name const & c, expr const & a1, expr const & a2) {
        return mk_app(c, {a1, a2});
    }

    expr mk_app(name const & c, expr const & a1, expr const & a2, expr const & a3) {
        return mk_app(c, {a1, a2, a3});
    }

    expr mk_app(name const & c, unsigned mask_sz, bool const * mask, expr const * args) {
        type_context_old::tmp_mode_scope scope(m_ctx);
        unsigned nargs = get_nargs(mask_sz, mask);
        optional<entry> e = get_entry(c, mask_sz, mask);
        if (!e) {
            trace_failure(c, "failed to retrieve declaration");
            throw app_builder_exception();
        }
        init_ctx_for(*e);
        unsigned i    = mask_sz;
        unsigned j    = nargs;
        list<expr> it = e->m_expl_args;
        while (i > 0) {
            --i;
            if (mask[i]) {
                --j;
                expr const & m = head(it);
                if (!m_ctx.is_def_eq(m, args[j])) {
                    trace_unify_failure(c, j, m, args[j]);
                    throw app_builder_exception();
                }
                it = tail(it);
            }
        }
        if (!check_all_assigned(*e)) {
            trace_failure(c, "there are missing implicit arguments");
            throw app_builder_exception();
        }
        return m_ctx.instantiate_mvars(e->m_app);
    }

    /** \brief Shortcut for mk_app(c, total_nargs, mask, expl_nargs), where
        \c mask starts with total_nargs - expl_nargs false's followed by expl_nargs true's
        \pre total_nargs >= expl_nargs */
    expr mk_app(name const & c, unsigned total_nargs, unsigned expl_nargs, expr const * expl_args) {
        lean_assert(total_nargs >= expl_nargs);
        buffer<bool> mask;
        mask.resize(total_nargs - expl_nargs, false);
        mask.resize(total_nargs, true);
        return mk_app(c, mask.size(), mask.data(), expl_args);
    }

    expr mk_app(name const & c, unsigned total_nargs, std::initializer_list<expr> const & args) {
        return mk_app(c, total_nargs, args.size(), args.begin());
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1) {
        return mk_app(c, total_nargs, {a1});
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1, expr const & a2) {
        return mk_app(c, total_nargs, {a1, a2});
    }

    expr mk_app(name const & c, unsigned total_nargs, expr const & a1, expr const & a2, expr const & a3) {
        return mk_app(c, total_nargs, {a1, a2, a3});
    }

    /** \brief Similar to mk_app(n, lhs, rhs), but handles eq and iff more efficiently. */
    expr mk_rel(name const & n, expr const & lhs, expr const & rhs) {
        if (n == get_eq_name()) {
            return mk_eq(lhs, rhs);
        } else if (n == get_iff_name()) {
            return mk_iff(lhs, rhs);
        } else if (auto info = get_relation_info(env(), n)) {
            buffer<bool> mask;
            for (unsigned i = 0; i < info->get_arity(); i++) {
                mask.push_back(i == info->get_lhs_pos() || i == info->get_rhs_pos());
            }
            expr args[2] = {lhs, rhs};
            return mk_app(n, info->get_arity(), mask.data(), args);
        } else {
            // for unregistered relations assume lhs and rhs are the last two arguments.
            expr args[2] = {lhs, rhs};
            return mk_app(n, 2, args);
        }
    }

    expr mk_eq(expr const & a, expr const & b) {
        expr A    = m_ctx.infer(a);
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_name(), {lvl}), A, a, b);
    }

    expr mk_iff(expr const & a, expr const & b) {
        return ::lean::mk_app(mk_constant(get_iff_name()), a, b);
    }

    expr mk_heq(expr const & a, expr const & b) {
        expr A    = m_ctx.infer(a);
        expr B    = m_ctx.infer(b);
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_heq_name(), {lvl}), A, a, B, b);
    }

    /** \brief Similar a reflexivity proof for the given relation */
    expr mk_refl(name const & relname, expr const & a) {
        if (relname == get_eq_name()) {
            return mk_eq_refl(a);
        } else if (relname == get_iff_name()) {
            return mk_iff_refl(a);
        } else if (relname == get_heq_name()) {
            return mk_heq_refl(a);
        } else if (auto info = get_refl_extra_info(env(), relname)) {
            return mk_app(info->m_name, 1, &a);
        } else {
            lean_app_builder_trace(
                tout() << "failed to build reflexivity proof, '" << relname
                << "' is not registered as a reflexive relation\n";);
            throw app_builder_exception();
        }
    }
    expr mk_eq_refl(expr const & a) {
        expr A     = m_ctx.infer(a);
        level lvl  = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_refl_name(), {lvl}), A, a);
    }
    expr mk_iff_refl(expr const & a) {
        return ::lean::mk_app(mk_constant(get_iff_refl_name()), a);
    }
    expr mk_heq_refl(expr const & a) {
        expr A     = m_ctx.infer(a);
        level lvl  = get_level(A);
        return ::lean::mk_app(mk_constant(get_heq_refl_name(), {lvl}), A, a);
    }

    /** \brief Similar a symmetry proof for the given relation */
    expr mk_symm(name const & relname, expr const & H) {
        if (relname == get_eq_name()) {
            return mk_eq_symm(H);
        } else if (relname == get_iff_name()) {
            return mk_iff_symm(H);
        } else if (relname == get_heq_name()) {
            return mk_heq_symm(H);
        } else if (auto info = get_symm_extra_info(env(), relname)) {
            return mk_app(info->m_name, 1, &H);
        } else {
            lean_app_builder_trace(
                tout() << "failed to build symmetry proof, '" << relname
                << "' is not registered as a symmetric relation\n";);
            throw app_builder_exception();
        }
    }
    expr mk_eq_symm(expr const & H) {
        if (is_app_of(H, get_eq_refl_name()))
            return H;
        expr p    = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, lhs, rhs;
        if (!is_eq(p, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build eq.symm, equality expected:\n" << p << "\n";);
            throw app_builder_exception();
        }
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, lhs, rhs, H);
    }
    expr mk_eq_symm(expr const & a, expr const & b, expr const & H) {
        expr A    = m_ctx.infer(a);
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, a, b, H);
    }
    expr mk_iff_symm(expr const & H) {
        expr p    = m_ctx.infer(H);
        expr lhs, rhs;
        if (is_iff(p, lhs, rhs)) {
            return ::lean::mk_app(mk_constant(get_iff_symm_name()), lhs, rhs, H);
        } else {
            return mk_app(get_iff_symm_name(), {H});
        }
    }
    expr mk_heq_symm(expr const & H) {
        expr p     = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, a, B, b;
        if (!is_heq(p, A, a, B, b)) {
            lean_app_builder_trace(tout() << "failed to build heq.symm, heterogeneous equality expected:\n" << p << "\n";);
            throw app_builder_exception();
        }
        level lvl = get_level(A);
        return ::lean::mk_app({mk_constant(get_heq_symm_name(), {lvl}), A, B, a, b, H});
    }

    /** \brief Similar a transitivity proof for the given relation */
    expr mk_trans(name const & relname, expr const & H1, expr const & H2) {
        if (relname == get_eq_name()) {
            return mk_eq_trans(H1, H2);
        } else if (relname == get_iff_name()) {
            return mk_iff_trans(H1, H2);
        } else if (relname == get_heq_name()) {
            return mk_heq_trans(H1, H2);
        } else if (auto info = get_trans_extra_info(env(), relname, relname)) {
            expr args[2] = {H1, H2};
            return mk_app(info->m_name, 2, args);
        } else {
            lean_app_builder_trace(
                tout() << "failed to build symmetry proof, '" << relname
                << "' is not registered as a transitive relation\n";);
            throw app_builder_exception();
        }
    }
    expr mk_eq_trans(expr const & H1, expr const & H2) {
        if (is_app_of(H1, get_eq_refl_name()))
            return H2;
        if (is_app_of(H2, get_eq_refl_name()))
            return H1;
        expr p1    = m_ctx.relaxed_whnf(m_ctx.infer(H1));
        expr p2    = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A, lhs1, rhs1, lhs2, rhs2;
        if (!is_eq(p1, A, lhs1, rhs1) || !is_eq(p2, lhs2, rhs2)) {
            lean_app_builder_trace(
                tout() << "failed to build eq.trans, equality expected:\n"
                << p1 << "\n" << p2 << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A);
        return ::lean::mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, lhs1, rhs1, rhs2, H1, H2});
    }
    expr mk_eq_trans(expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2) {
        if (is_app_of(H1, get_eq_refl_name()))
            return H2;
        if (is_app_of(H2, get_eq_refl_name()))
            return H1;
        expr A    = m_ctx.infer(a);
        level lvl = get_level(A);
        return ::lean::mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, a, b, c, H1, H2});
    }
    expr mk_iff_trans(expr const & H1, expr const & H2) {
        expr p1    = m_ctx.infer(H1);
        expr p2    = m_ctx.infer(H2);
        expr lhs1, rhs1, lhs2, rhs2;
        if (is_iff(p1, lhs1, rhs1) && is_iff(p2, lhs2, rhs2)) {
            return ::lean::mk_app({mk_constant(get_iff_trans_name()), lhs1, rhs1, rhs2, H1, H2});
        } else {
            return mk_app(get_iff_trans_name(), {H1, H2});
        }
    }
    expr mk_heq_trans(expr const & H1, expr const & H2) {
        expr p1    = m_ctx.relaxed_whnf(m_ctx.infer(H1));
        expr p2    = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A1, a1, B1, b1, A2, a2, B2, b2;
        if (!is_heq(p1, A1, a1, B1, b1) || !is_heq(p2, A2, a2, B2, b2)) {
            lean_app_builder_trace(
                tout() << "failed to build heq.trans, heterogeneous equality expected:\n"
                << p1 << "\n" << p2 << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A1);
        return ::lean::mk_app({mk_constant(get_heq_trans_name(), {lvl}), A1, B1, B2, a1, b1, b2, H1, H2});
    }

    expr mk_eq_rec(expr const & motive, expr const & H1, expr const & H2) {
        if (is_constant(get_app_fn(H2), get_eq_refl_name()))
            return H1;
        expr p       = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A, lhs, rhs;
        if (!is_eq(p, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build eq.rec, equality proof expected:\n" << H2 << "\n";);
            throw app_builder_exception();
        }
        level A_lvl = get_level(A);
        expr mtype  = m_ctx.relaxed_whnf(m_ctx.infer(motive));
        if (!is_pi(mtype) || !is_sort(binding_body(mtype))) {
            lean_app_builder_trace(tout() << "failed to build eq.rec, invalid motive:\n" << motive << "\n";);
            throw app_builder_exception();
        }
        level l_1    = sort_level(binding_body(mtype));
        name const & eqrec = get_eq_rec_name();
        return ::lean::mk_app({mk_constant(eqrec, {l_1, A_lvl}), A, lhs, motive, H1, rhs, H2});
    }

    expr mk_eq_drec(expr const & motive, expr const & H1, expr const & H2) {
        if (is_constant(get_app_fn(H2), get_eq_refl_name()))
            return H1;
        expr p       = m_ctx.relaxed_whnf(m_ctx.infer(H2));
        expr A, lhs, rhs;
        if (!is_eq(p, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build eq.drec, equality proof expected:\n" << H2 << "\n";);
            throw app_builder_exception();
        }
        level A_lvl = get_level(A);
        expr mtype  = m_ctx.relaxed_whnf(m_ctx.infer(motive));
        if (!is_pi(mtype) || !is_pi(binding_body(mtype)) || !is_sort(binding_body(binding_body(mtype)))) {
            lean_app_builder_trace(tout() << "failed to build eq.drec, invalid motive:\n" << motive << "\n";);
            throw app_builder_exception();
        }
        level l_1    = sort_level(binding_body(binding_body(mtype)));
        name const & eqrec = get_eq_drec_name();
        return ::lean::mk_app({mk_constant(eqrec, {l_1, A_lvl}), A, lhs, motive, H1, rhs, H2});
    }

    expr mk_eq_of_heq(expr const & H) {
        if (is_constant(get_app_fn(H), get_heq_of_eq_name()))
            return app_arg(H);
        expr p    = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, a, B, b;
        if (!is_heq(p, A, a, B, b)) {
            lean_app_builder_trace(tout() << "failed to build eq_of_heq, heterogeneous equality proof expected:\n" << H << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A);
        return ::lean::mk_app({mk_constant(get_eq_of_heq_name(), {lvl}), A, a, b, H});
    }

    expr mk_heq_of_eq(expr const & H) {
        if (is_constant(get_app_fn(H), get_eq_of_heq_name()))
            return app_arg(H);
        expr p    = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr A, a, b;
        if (!is_eq(p, A, a, b)) {
            lean_app_builder_trace(tout() << "failed to build heq_of_eq equality proof expected:\n" << H << "\n";);
            throw app_builder_exception();
        }
        level lvl  = get_level(A);
        return ::lean::mk_app({mk_constant(get_heq_of_eq_name(), {lvl}), A, a, b, H});
    }

    /** \brief Given a reflexive relation R, and a proof H : a = b,
        build a proof for (R a b) */
    expr lift_from_eq(name const & R, expr const & H) {
        if (R == get_eq_name())
            return H;
        expr H_type = m_ctx.relaxed_whnf(m_ctx.infer(H));
        // H_type : @eq A a b
        expr A, a, b;
        if (!is_eq(H_type, A, a, b)) {
            lean_app_builder_trace(tout() << "failed to build lift_of_eq equality proof expected:\n" << H << "\n";);
            throw app_builder_exception();
        }
        type_context_old::tmp_locals locals(m_ctx);
        expr x         = locals.push_local(name("A"), A);
        // motive := fun x : A, a ~ x
        expr motive    = locals.mk_lambda(mk_rel(R, a, x));
        // minor : a ~ a
        expr minor     = mk_refl(R, a);
        return mk_eq_rec(motive, minor, H);
    }

    expr mk_partial_add(expr const & A) {
        level lvl = get_level(A);
        auto A_has_add = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_add_name(), {lvl}), A));
        if (!A_has_add) {
            trace_inst_failure(A, "has_add");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_add_add_name(), {lvl}), A, *A_has_add);
    }

    expr mk_partial_mul(expr const & A) {
        level lvl = get_level(A);
        auto A_has_mul = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_mul_name(), {lvl}), A));
        if (!A_has_mul) {
            trace_inst_failure(A, "has_mul");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_mul_mul_name(), {lvl}), A, *A_has_mul);
    }

    expr mk_zero(expr const & A) {
        level lvl = get_level(A);
        auto A_has_zero = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_zero_name(), {lvl}), A));
        if (!A_has_zero) {
            trace_inst_failure(A, "has_zero");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_zero_zero_name(), {lvl}), A, *A_has_zero);
    }

    expr mk_one(expr const & A) {
        level lvl = get_level(A);
        auto A_has_one = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_has_one_name(), {lvl}), A));
        if (!A_has_one) {
            trace_inst_failure(A, "has_one");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_has_one_one_name(), {lvl}), A, *A_has_one);
    }

    expr mk_partial_left_distrib(expr const & A) {
        level lvl = get_level(A);
        auto A_distrib = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_distrib_name(), {lvl}), A));
        if (!A_distrib) {
            trace_inst_failure(A, "distrib");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_left_distrib_name(), {lvl}), A, *A_distrib);
    }

    expr mk_partial_right_distrib(expr const & A) {
        level lvl = get_level(A);
        auto A_distrib = m_ctx.mk_class_instance(::lean::mk_app(mk_constant(get_distrib_name(), {lvl}), A));
        if (!A_distrib) {
            trace_inst_failure(A, "distrib");
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_right_distrib_name(), {lvl}), A, *A_distrib);
    }

    expr mk_ss_elim(expr const & A, expr const & ss_inst, expr const & old_e, expr const & new_e) {
        level lvl = get_level(A);
        return ::lean::mk_app(mk_constant(get_subsingleton_elim_name(), {lvl}), A, ss_inst, old_e, new_e);
    }

    expr mk_false_rec(expr const & c, expr const & H) {
        level c_lvl = get_level(c);
        return ::lean::mk_app(mk_constant(get_false_rec_name(), {c_lvl}), c, H);
    }

    expr mk_congr_arg(expr const & f, expr const & H, bool skip_arrow_test) {
        expr eq = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr pi = m_ctx.relaxed_whnf(m_ctx.infer(f));
        expr A, B, lhs, rhs;
        if (!is_eq(eq, A, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build congr_arg, equality expected:\n" << eq << "\n";);
            throw app_builder_exception();
        }
        if (!skip_arrow_test && !is_arrow(pi)) {
            lean_app_builder_trace(tout() << "failed to build congr_arg, non-dependent function expected:\n" << pi << "\n";);
            throw app_builder_exception();
        }
        B = binding_body(pi);
        level lvl_1  = get_level(A);
        level lvl_2  = get_level(B);
        return ::lean::mk_app({mk_constant(get_congr_arg_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, f, H});
    }

    expr mk_eq_true_intro(expr const & H) {
        expr p = m_ctx.infer(H);
        return ::lean::mk_app(mk_constant(get_eq_true_intro_name()), p, H);
    }

    expr mk_eq_false_intro(expr const & H) {
        expr not_p = m_ctx.relaxed_whnf(m_ctx.infer(H));
        if (!is_pi(not_p)) {
            lean_app_builder_trace(tout() << "failed to build eq_false_intro, negation expected:\n" << not_p << "\n";);
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_eq_false_intro_name()), binding_domain(not_p), H);
    }

    expr mk_of_eq_true(expr const & H) {
        if (is_constant(get_app_fn(H), get_eq_true_intro_name())) {
            // of_eq_true (eq_true_intro H) == H
            return app_arg(H);
        }
        expr eq = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr lhs, rhs;
        if (!is_eq(eq, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build of_eq_true, equality expected:\n" << eq << "\n";);
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_of_eq_true_name()), lhs, H);
    }

    expr mk_not_of_eq_false(expr const & H) {
        if (is_constant(get_app_fn(H), get_eq_false_intro_name())) {
            // not_of_eq_false (eq_false_intro H) == H
            return app_arg(H);
        }
        expr eq = m_ctx.relaxed_whnf(m_ctx.infer(H));
        expr lhs, rhs;
        if (!is_eq(eq, lhs, rhs)) {
            lean_app_builder_trace(tout() << "failed to build not_of_eq_false, equality expected:\n" << eq << "\n";);
            throw app_builder_exception();
        }
        return ::lean::mk_app(mk_constant(get_not_of_eq_false_name()), lhs, H);
    }
};

expr mk_app(type_context_old & ctx, name const & c, unsigned nargs, expr const * args, optional<transparency_mode> const & md) {
    if (md) {
        type_context_old::transparency_scope _s1(ctx, *md);
        type_context_old::zeta_scope         _s2(ctx, true);
        return app_builder(ctx).mk_app(c, nargs, args);
    } else if (!is_at_least_semireducible(ctx.mode())) {
        type_context_old::transparency_scope _s1(ctx, transparency_mode::Semireducible);
        type_context_old::zeta_scope _s2(ctx, true);
        return app_builder(ctx).mk_app(c, nargs, args);
    } else {
        return app_builder(ctx).mk_app(c, nargs, args);
    }
}

expr mk_app(type_context_old & ctx, name const & c, unsigned mask_sz, bool const * mask, expr const * args) {
    return app_builder(ctx).mk_app(c, mask_sz, mask, args);
}

expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, unsigned expl_nargs, expr const * expl_args) {
    return app_builder(ctx).mk_app(c, total_nargs, expl_nargs, expl_args);
}

expr mk_rel(type_context_old & ctx, name const & n, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_rel(n, lhs, rhs);
}

expr mk_eq(type_context_old & ctx, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_eq(lhs, rhs);
}

expr mk_iff(type_context_old & ctx, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_iff(lhs, rhs);
}

expr mk_heq(type_context_old & ctx, expr const & lhs, expr const & rhs) {
    return app_builder(ctx).mk_heq(lhs, rhs);
}

expr mk_refl(type_context_old & ctx, name const & relname, expr const & a) {
    return app_builder(ctx).mk_refl(relname, a);
}

expr mk_eq_refl(type_context_old & ctx, expr const & a) {
    return app_builder(ctx).mk_eq_refl(a);
}

expr mk_iff_refl(type_context_old & ctx, expr const & a) {
    return app_builder(ctx).mk_iff_refl(a);
}

expr mk_heq_refl(type_context_old & ctx, expr const & a) {
    return app_builder(ctx).mk_heq_refl(a);
}

expr mk_symm(type_context_old & ctx, name const & relname, expr const & H) {
    return app_builder(ctx).mk_symm(relname, H);
}

expr mk_eq_symm(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_symm(H);
}

expr mk_eq_symm(type_context_old & ctx, expr const & a, expr const & b, expr const & H) {
    return app_builder(ctx).mk_eq_symm(a, b, H);
}

expr mk_iff_symm(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_iff_symm(H);
}

expr mk_heq_symm(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_heq_symm(H);
}

expr mk_trans(type_context_old & ctx, name const & relname, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_trans(relname, H1, H2);
}

expr mk_eq_trans(type_context_old & ctx, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_trans(H1, H2);
}

expr mk_eq_trans(type_context_old & ctx, expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_trans(a, b, c, H1, H2);
}

expr mk_iff_trans(type_context_old & ctx, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_iff_trans(H1, H2);
}

expr mk_heq_trans(type_context_old & ctx, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_heq_trans(H1, H2);
}

expr mk_eq_rec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_rec(C, H1, H2);
}

expr mk_eq_drec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2) {
    return app_builder(ctx).mk_eq_drec(C, H1, H2);
}

expr mk_eq_of_heq(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_of_heq(H);
}

expr mk_heq_of_eq(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_heq_of_eq(H);
}

expr mk_congr_arg(type_context_old & ctx, expr const & f, expr const & H, bool skip_arrow_test) {
    expr eq = ctx.relaxed_whnf(ctx.infer(H));
    expr pi = ctx.relaxed_whnf(ctx.infer(f));
    expr A, B, lhs, rhs;
    if (!is_eq(eq, A, lhs, rhs)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr_arg, equality expected:\n" << eq << "\n";);
        throw app_builder_exception();
    }
    if (!is_arrow(pi)) {
        if (!skip_arrow_test || !is_pi(pi)) {
            lean_app_builder_trace_core(ctx, tout() << "failed to build congr_arg, non-dependent function expected:\n" << pi << "\n";);
            throw app_builder_exception();
        } else {
            B = instantiate(binding_body(pi), lhs);
        }
    } else {
        B = binding_body(pi);
    }
    level lvl_1  = get_level_ap(ctx, A);
    level lvl_2  = get_level_ap(ctx, B);
    return mk_app({mk_constant(get_congr_arg_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, f, H});
}

expr mk_congr_fun(type_context_old & ctx, expr const & H, expr const & a) {
    expr eq = ctx.relaxed_whnf(ctx.infer(H));
    expr pi, lhs, rhs;
    if (!is_eq(eq, pi, lhs, rhs)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr_fun, equality expected:\n" << eq << "\n";);
        throw app_builder_exception();
    }
    pi = ctx.relaxed_whnf(pi);
    if (!is_pi(pi)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr_fun, function expected:\n" << pi << "\n";);
        throw app_builder_exception();
    }
    expr A       = binding_domain(pi);
    expr B       = mk_lambda(binding_name(pi), binding_domain(pi), binding_body(pi), binding_info(pi));
    level lvl_1  = get_level_ap(ctx, A);
    level lvl_2  = get_level_ap(ctx, mk_app(B, a));
    return mk_app({mk_constant(get_congr_fun_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, H, a});
}

expr mk_congr(type_context_old & ctx, expr const & H1, expr const & H2, bool skip_arrow_test) {
    expr eq1 = ctx.relaxed_whnf(ctx.infer(H1));
    expr eq2 = ctx.relaxed_whnf(ctx.infer(H2));
    expr pi, lhs1, rhs1;
    if (!is_eq(eq1, pi, lhs1, rhs1)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr, equality expected:\n" << eq1 << "\n";);
        throw app_builder_exception();
    }
    expr lhs2, rhs2;
    if (!is_eq(eq2, lhs2, rhs2)) {
        lean_app_builder_trace_core(ctx, tout() << "failed to build congr, equality expected:\n" << eq2 << "\n";);
        throw app_builder_exception();
    }
    pi = ctx.relaxed_whnf(pi);
    expr A, B;
    if (!is_arrow(pi)) {
        if (!skip_arrow_test || !is_pi(pi)) {
            lean_app_builder_trace_core(ctx, tout() << "failed to build congr, non-dependent function expected:\n" << pi << "\n";);
            throw app_builder_exception();
        } else {
            B = instantiate(binding_body(pi), lhs2);
        }
    } else {
        B = binding_body(pi);
    }
    A            = binding_domain(pi);
    level lvl_1  = get_level_ap(ctx, A);
    level lvl_2  = get_level_ap(ctx, B);
    return mk_app({mk_constant(get_congr_name(), {lvl_1, lvl_2}), A, B, lhs1, rhs1, lhs2, rhs2, H1, H2});
}

expr mk_funext(type_context_old & ctx, expr const & lam_pf) {
    // TODO(dhs): efficient version
    return mk_app(ctx, get_funext_name(), lam_pf);
}

expr lift_from_eq(type_context_old & ctx, name const & R, expr const & H) {
    return app_builder(ctx).lift_from_eq(R, H);
}

expr mk_iff_false_intro(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_iff_false_intro_name(), {H});
}

expr mk_iff_true_intro(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_iff_true_intro_name(), {H});
}

expr mk_eq_false_intro(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_false_intro(H);
}

expr mk_eq_true_intro(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_eq_true_intro(H);
}

expr mk_not_of_eq_false(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_not_of_eq_false(H);
}

expr mk_of_eq_true(type_context_old & ctx, expr const & H) {
    return app_builder(ctx).mk_of_eq_true(H);
}

expr mk_neq_of_not_iff(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_neq_of_not_iff_name(), {H});
}

expr mk_not_of_iff_false(type_context_old & ctx, expr const & H) {
    if (is_constant(get_app_fn(H), get_iff_false_intro_name())) {
        // not_of_iff_false (iff_false_intro H) == H
        return app_arg(H);
    }
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_not_of_iff_false_name(), 2, {H});
}

expr mk_of_iff_true(type_context_old & ctx, expr const & H) {
    if (is_constant(get_app_fn(H), get_iff_true_intro_name())) {
        // of_iff_true (iff_true_intro H) == H
        return app_arg(H);
    }
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_of_iff_true_name(), {H});
}

expr mk_false_of_true_iff_false(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_false_of_true_iff_false_name(), {H});
}

expr mk_false_of_true_eq_false(type_context_old & ctx, expr const & H) {
    // TODO(Leo): implement custom version if bottleneck.
    return mk_app(ctx, get_false_of_true_eq_false_name(), {H});
}

expr mk_not(type_context_old & ctx, expr const & H) {
    // TODO(dhs): implement custom version if bottleneck.
    return mk_app(ctx, get_not_name(), {H});
}

expr mk_absurd(type_context_old & ctx, expr const & Hp, expr const & Hnp, expr const & b) {
    return mk_app(ctx, get_absurd_name(), {b, Hp, Hnp});
}

expr mk_partial_add(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_add(A);
}

expr mk_partial_mul(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_mul(A);
}

expr mk_zero(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_zero(A);
}

expr mk_one(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_one(A);
}

expr mk_partial_left_distrib(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_left_distrib(A);
}

expr mk_partial_right_distrib(type_context_old & ctx, expr const & A) {
    return app_builder(ctx).mk_partial_right_distrib(A);
}

expr mk_ss_elim(type_context_old & ctx, expr const & A, expr const & ss_inst, expr const & old_e, expr const & new_e) {
    return app_builder(ctx).mk_ss_elim(A, ss_inst, old_e, new_e);
}

expr mk_false_rec(type_context_old & ctx, expr const & c, expr const & H) {
    return app_builder(ctx).mk_false_rec(c, H);
}

expr mk_ite(type_context_old & ctx, expr const & c, expr const & t, expr const & e) {
    bool mask[5] = {true, false, false, true, true};
    expr args[3] = {c, t, e};
    return mk_app(ctx, get_ite_name(), 5, mask, args);
}

expr mk_id(type_context_old & ctx, expr const & type, expr const & h) {
    level lvl = get_level_ap(ctx, type);
    return mk_app(mk_constant(get_id_name(), {lvl}), type, h);
}

expr mk_id(type_context_old & ctx, expr const & h) {
    return mk_id(ctx, ctx.infer(h), h);
}

expr mk_id_rhs(type_context_old & ctx, expr const & h) {
    expr type = ctx.infer(h);
    level lvl = get_level_ap(ctx, type);
    return mk_app(mk_constant(get_id_rhs_name(), {lvl}), type, h);
}

expr mk_id_delta(type_context_old & ctx, expr const & h) {
    expr type = ctx.infer(h);
    level lvl = get_level_ap(ctx, type);
    return mk_app(mk_constant(get_id_delta_name(), {lvl}), type, h);
}

static bool is_eq_trans(expr const & h, expr & h1, expr & h2) {
    if (is_app_of(h, get_eq_trans_name(), 6)) {
        h1 = app_arg(app_fn(h));
        h2 = app_arg(h);
        return true;
    } else {
        return false;
    }
}

static bool is_propext(expr const & h, expr & h1) {
    if (is_app_of(h, get_propext_name(), 3)) {
        h1 = app_arg(h);
        return true;
    } else {
        return false;
    }
}

static bool is_eq_self_iff_true(expr const & h, expr & t) {
    if (is_app_of(h, get_eq_self_iff_true_name(), 2)) {
        t = app_arg(h);
        return true;
    } else {
        return false;
    }
}

expr mk_eq_mpr(type_context_old & ctx, expr const & h1, expr const & h2) {
    /*
       eq.mpr (eq.trans H (propext (@eq_self_iff_true t))) h2
       ==>
       eq.mpr H (eq.refl t)

       Remark: note that (h2 : true)
    */
    expr H, P, E, t;
    if (is_eq_trans(h1, H, P) && is_propext(P, E) && is_eq_self_iff_true(E, t)) {
        return mk_app(ctx, get_eq_mpr_name(), H, mk_eq_refl(ctx, t));
    }
    return mk_app(ctx, get_eq_mpr_name(), h1, h2);
}

expr mk_iff_mpr(type_context_old & ctx, expr const & h1, expr const & h2) {
    return mk_app(ctx, get_iff_mpr_name(), h1, h2);
}

expr mk_eq_mp(type_context_old & ctx, expr const & h1, expr const & h2) {
    return mk_app(ctx, get_eq_mp_name(), h1, h2);
}

expr mk_iff_mp(type_context_old & ctx, expr const & h1, expr const & h2) {
    return mk_app(ctx, get_iff_mp_name(), h1, h2);
}

void initialize_app_builder() {
    register_trace_class("app_builder");
    register_thread_local_reset_fn([]() { get_abch().clear(); });
}
void finalize_app_builder() {}
}

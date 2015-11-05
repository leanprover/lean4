/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/scoped_map.h"
#include "util/name_map.h"
#include "kernel/instantiate.h"
#include "library/match.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/kernel_bindings.h"
#include "library/tmp_type_context.h"
#include "library/relation_manager.h"

namespace lean {
struct app_builder::imp {
    tmp_type_context * m_ctx;
    bool               m_ctx_owner;

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

        template<typename It>
        static bool is_simple(It const & begin, It const & end) {
            bool found_true = false;
            for (auto it = begin; it != end; ++it) {
                auto b = *it;
                if (b) {
                    found_true = true;
                } else if (found_true) {
                    // found (true, false)
                    return false;
                }
            }
            return true;
        }

        static bool is_simple(list<bool> const & mask) {
            return is_simple(mask.begin(), mask.end());
        }

        key(name const & c, unsigned n):
            m_name(c), m_num_expl(n),
            m_hash(::lean::hash(c.hash(), n)) {
        }

        key(name const & c, list<bool> const & m):
            m_name(c), m_num_expl(length(m)) {
            m_hash = ::lean::hash(c.hash(), m_num_expl);
            if (!is_simple(m)) {
                m_mask = m;
                for (bool b : m) {
                    if (b)
                        m_hash = ::lean::hash(m_hash, 17u);
                    else
                        m_hash = ::lean::hash(m_hash, 31u);
                }
            }
        }

        bool check_invariant() const {
            lean_assert(empty(m_mask) || length(m_mask) == m_num_expl);
            lean_assert(empty(m_mask) || !is_simple(m_mask));
            return true;
        }

        unsigned hash() const {
            return m_hash;
        }

        friend bool operator==(key const & k1, key const & k2) {
            return k1.m_name == k2.m_name && k1.m_num_expl == k2.m_num_expl && k1.m_mask == k2.m_mask;
        }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.hash(); }
    };

    typedef std::unordered_map<key, entry, key_hash_fn> map;

    map               m_map;
    refl_info_getter  m_refl_getter;
    symm_info_getter  m_symm_getter;
    trans_info_getter m_trans_getter;

    imp(tmp_type_context & ctx, bool owner):
        m_ctx(&ctx),
        m_ctx_owner(owner),
        m_refl_getter(mk_refl_info_getter(m_ctx->env())),
        m_symm_getter(mk_symm_info_getter(m_ctx->env())),
        m_trans_getter(mk_trans_info_getter(m_ctx->env())) {
    }

    imp(environment const & env, io_state const & ios, reducible_behavior b):
        imp(*new tmp_type_context(env, ios, b), true) {
    }

    imp(tmp_type_context & ctx):
        imp(ctx, false) {
    }

    ~imp() {
        lean_assert(m_ctx);
        if (m_ctx_owner)
            delete m_ctx;
    }

    levels mk_metavars(declaration const & d, buffer<expr> & mvars, buffer<optional<expr>> & inst_args) {
        m_ctx->clear();
        unsigned num_univ = d.get_num_univ_params();
        buffer<level> lvls_buffer;
        for (unsigned i = 0; i < num_univ; i++) {
            lvls_buffer.push_back(m_ctx->mk_uvar());
        }
        levels lvls = to_list(lvls_buffer);
        expr type   = m_ctx->whnf(instantiate_type_univ_params(d, lvls));
        while (is_pi(type)) {
            expr mvar = m_ctx->mk_mvar(binding_domain(type));
            if (binding_info(type).is_inst_implicit())
                inst_args.push_back(some_expr(mvar));
            else
                inst_args.push_back(none_expr());
            mvars.push_back(mvar);
            type = m_ctx->whnf(instantiate(binding_body(type), mvar));
        }
        return lvls;
    }

    optional<entry> get_entry(name const & c, unsigned nargs) {
        key k(c, nargs);
        lean_assert(k.check_invariant());
        auto it = m_map.find(k);
        if (it == m_map.end()) {
            if (auto d = m_ctx->env().find(c)) {
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
                m_map.insert(mk_pair(k, e));
                return optional<entry>(e);
            } else {
                return optional<entry>(); // unknown decl
            }
        } else {
            return optional<entry>(it->second);
        }
    }

    optional<entry> get_entry(name const & c, unsigned mask_sz, bool const * mask) {
        key k(c, to_list(mask, mask+mask_sz));
        lean_assert(k.check_invariant());
        auto it = m_map.find(k);
        if (it == m_map.end()) {
            if (auto d = m_ctx->env().find(c)) {
                buffer<expr> mvars;
                buffer<optional<expr>> inst_args;
                levels lvls = mk_metavars(*d, mvars, inst_args);
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
                m_map.insert(mk_pair(k, e));
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
            if (inst_arg) {
                expr type = m_ctx->instantiate_uvars_mvars(mlocal_type(*inst_arg));
                if (auto v = m_ctx->mk_class_instance(type)) {
                    if (!m_ctx->force_assign(*inst_arg, *v))
                        return false;
                } else {
                    return false;
                }
            }
            if (!m_ctx->is_mvar_assigned(i))
                return false;
        }
        for (unsigned i = 0; i < e.m_num_umeta; i++) {
            if (!m_ctx->is_uvar_assigned(i))
                return false;
        }
        return true;
    }

    void init_ctx_for(entry const & e) {
        m_ctx->clear();
        m_ctx->set_next_uvar_idx(e.m_num_umeta);
        m_ctx->set_next_mvar_idx(e.m_num_emeta);
    }

    optional<expr> mk_app(name const & c, unsigned nargs, expr const * args) {
        optional<entry> e = get_entry(c, nargs);
        if (!e)
            return none_expr();
        init_ctx_for(*e);
        unsigned i = nargs;
        for (auto m : e->m_expl_args) {
            if (i == 0)
                return none_expr();
            --i;
            if (!m_ctx->assign(m, args[i]))
                return none_expr();
        }
        if (!check_all_assigned(*e))
            return none_expr();
        return some_expr(m_ctx->instantiate_uvars_mvars(e->m_app));
    }

    static unsigned get_nargs(unsigned mask_sz, bool const * mask) {
        unsigned nargs = 0;
        for (unsigned i = 0; i < mask_sz; i++) {
            if (mask[i])
                nargs++;
        }
        return nargs;
    }

    optional<expr> mk_app(name const & c, unsigned mask_sz, bool const * mask, expr const * args) {
        unsigned nargs = get_nargs(mask_sz, mask);
        if (key::is_simple(mask, mask + mask_sz)) {
            return mk_app(c, nargs, args);
        } else {
            optional<entry> e = get_entry(c, mask_sz, mask);
            if (!e)
                return none_expr();
            init_ctx_for(*e);
            unsigned i    = mask_sz;
            unsigned j    = nargs;
            list<expr> it = e->m_expl_args;
            while (i > 0) {
                --i;
                if (mask[i]) {
                    --j;
                    expr const & m = head(it);
                    if (!m_ctx->assign(m, args[j]))
                        return none_expr();
                    it = tail(it);
                }
            }
            if (!check_all_assigned(*e))
                return none_expr();
            return some_expr(m_ctx->instantiate_uvars_mvars(e->m_app));
        }
    }

    optional<level> get_level(expr const & A) {
        expr Type = m_ctx->whnf(m_ctx->infer(A));
        if (!is_sort(Type))
            return none_level();
        return some_level(sort_level(Type));
    }

    optional<expr> mk_eq(expr const & a, expr const & b) {
        expr A    = m_ctx->infer(a);
        auto lvl  = get_level(A);
        if (!lvl)
            return none_expr();
        return some_expr(::lean::mk_app(mk_constant(get_eq_name(), {*lvl}), A, a, b));
    }

    optional<expr> mk_iff(expr const & a, expr const & b) {
        return some_expr(::lean::mk_app(mk_constant(get_iff_name()), a, b));
    }

    optional<expr> mk_eq_refl(expr const & a) {
        expr A    = m_ctx->infer(a);
        auto lvl  = get_level(A);
        if (!lvl)
            return none_expr();
        return some_expr(::lean::mk_app(mk_constant(get_eq_refl_name(), {*lvl}), A, a));
    }

    optional<expr> mk_iff_refl(expr const & a) {
        return some_expr(::lean::mk_app(mk_constant(get_iff_refl_name()), a));
    }

    optional<expr> mk_eq_symm(expr const & H) {
        expr p    = m_ctx->whnf(m_ctx->infer(H));
        expr lhs, rhs;
        if (!is_eq(p, lhs, rhs))
            return none_expr();
        expr A    = m_ctx->infer(lhs);
        auto lvl  = get_level(A);
        if (!lvl)
            return none_expr();
        return some_expr(::lean::mk_app(mk_constant(get_eq_symm_name(), {*lvl}), A, lhs, rhs, H));
    }

    optional<expr> mk_iff_symm(expr const & H) {
        expr p    = m_ctx->whnf(m_ctx->infer(H));
        expr lhs, rhs;
        if (!is_iff(p, lhs, rhs))
            return none_expr();
        return some_expr(::lean::mk_app(mk_constant(get_iff_symm_name()), lhs, rhs, H));
    }

    optional<expr> mk_eq_trans(expr const & H1, expr const & H2) {
        expr p1    = m_ctx->whnf(m_ctx->infer(H1));
        expr p2    = m_ctx->whnf(m_ctx->infer(H2));
        expr lhs1, rhs1, lhs2, rhs2;
        if (!is_eq(p1, lhs1, rhs1) || !is_eq(p2, lhs2, rhs2))
            return none_expr();
        expr A     = m_ctx->infer(lhs1);
        auto lvl  = get_level(A);
        if (!lvl)
            return none_expr();
        return some_expr(::lean::mk_app({mk_constant(get_eq_trans_name(), {*lvl}), A, lhs1, rhs1, rhs2, H1, H2}));
    }

    optional<expr> mk_iff_trans(expr const & H1, expr const & H2) {
        expr p1    = m_ctx->whnf(m_ctx->infer(H1));
        expr p2    = m_ctx->whnf(m_ctx->infer(H2));
        expr lhs1, rhs1, lhs2, rhs2;
        if (!is_iff(p1, lhs1, rhs1) || !is_iff(p2, lhs2, rhs2))
            return none_expr();
        return some_expr(::lean::mk_app({mk_constant(get_iff_trans_name()), lhs1, rhs1, rhs2, H1, H2}));
    }

    optional<expr> mk_rel(name const & n, expr const & lhs, expr const & rhs) {
        if (n == get_eq_name()) {
            return mk_eq(lhs, rhs);
        } else if (n == get_iff_name()) {
            return mk_iff(lhs, rhs);
        } else {
            expr args[2] = {lhs, rhs};
            return mk_app(n, 2, args);
        }
    }

    optional<expr> mk_refl(name const & relname, expr const & a) {
        if (relname == get_eq_name()) {
            return mk_eq_refl(a);
        } else if (relname == get_iff_name()) {
            return mk_iff_refl(a);
        } else if (auto info = m_refl_getter(relname)) {
            return mk_app(info->m_name, 1, &a);
        } else {
            return none_expr();
        }
    }

    optional<expr> mk_symm(name const & relname, expr const & H) {
        if (relname == get_eq_name()) {
            return mk_eq_symm(H);
        } else if (relname == get_iff_name()) {
            return mk_iff_symm(H);
        } else if (auto info = m_symm_getter(relname)) {
            return mk_app(info->m_name, 1, &H);
        } else {
            return none_expr();
        }
    }

    optional<expr> mk_trans(name const & relname, expr const & H1, expr const & H2) {
        if (relname == get_eq_name()) {
            return mk_eq_trans(H1, H2);
        } else if (relname == get_iff_name()) {
            return mk_iff_trans(H1, H2);
        } else if (auto info = m_trans_getter(relname, relname)) {
            expr args[2] = {H1, H2};
            return mk_app(info->m_name, 2, args);
        } else {
            return none_expr();
        }
    }

    optional<expr> mk_eq_rec(expr const & motive, expr const & H1, expr const & H2) {
        expr p       = m_ctx->whnf(m_ctx->infer(H2));
        expr lhs, rhs;
        if (!is_eq(p, lhs, rhs))
            return none_expr();
        expr A      = m_ctx->infer(lhs);
        auto A_lvl  = get_level(A);
        expr mtype  = m_ctx->whnf(m_ctx->infer(motive));
        if (!is_pi(mtype) || !is_sort(binding_body(mtype)))
            return none_expr();
        level l_1    = sort_level(binding_body(mtype));
        name const & eqrec = is_standard(m_ctx->env()) ? get_eq_rec_name() : get_eq_nrec_name();
        return some_expr(::lean::mk_app({mk_constant(eqrec, {l_1, *A_lvl}), A, lhs, motive, H1, rhs, H2}));
    }

    optional<expr> mk_eq_drec(expr const & motive, expr const & H1, expr const & H2) {
        expr p       = m_ctx->whnf(m_ctx->infer(H2));
        expr lhs, rhs;
        if (!is_eq(p, lhs, rhs))
            return none_expr();
        expr A      = m_ctx->infer(lhs);
        auto A_lvl  = get_level(A);
        expr mtype  = m_ctx->whnf(m_ctx->infer(H1));
        if (!is_pi(mtype) || !is_pi(binding_body(mtype)) || !is_sort(binding_body(binding_body(mtype))))
            return none_expr();
        level l_1    = sort_level(binding_body(binding_body(mtype)));
        name const & eqrec = is_standard(m_ctx->env()) ? get_eq_drec_name() : get_eq_rec_name();
        return some_expr(::lean::mk_app({mk_constant(eqrec, {l_1, *A_lvl}), A, lhs, motive, H1, rhs, H2}));
    }
};

app_builder::app_builder(environment const & env, io_state const & ios, reducible_behavior b):
    m_ptr(new imp(env, ios, b)) {
}

app_builder::app_builder(environment const & env, reducible_behavior b):
    app_builder(env, get_dummy_ios(), b) {
}

app_builder::app_builder(tmp_type_context & ctx):
    m_ptr(new imp(ctx)) {
}

app_builder::~app_builder() {}

optional<expr> app_builder::mk_app(name const & c, unsigned nargs, expr const * args) {
    return m_ptr->mk_app(c, nargs, args);
}

optional<expr> app_builder::mk_app(name const & c, unsigned mask_sz, bool const * mask, expr const * args) {
    return m_ptr->mk_app(c, mask_sz, mask, args);
}

optional<expr> app_builder::mk_rel(name const & n, expr const & lhs, expr const & rhs) {
    return m_ptr->mk_rel(n, lhs, rhs);
}

optional<expr> app_builder::mk_eq(expr const & lhs, expr const & rhs) {
    return m_ptr->mk_eq(lhs, rhs);
}

optional<expr> app_builder::mk_iff(expr const & lhs, expr const & rhs) {
    return m_ptr->mk_iff(lhs, rhs);
}

optional<expr> app_builder::mk_refl(name const & relname, expr const & a) {
    return m_ptr->mk_refl(relname, a);
}

optional<expr> app_builder::mk_eq_refl(expr const & a) {
    return m_ptr->mk_eq_refl(a);
}

optional<expr> app_builder::mk_iff_refl(expr const & a) {
    return m_ptr->mk_iff_refl(a);
}

optional<expr> app_builder::mk_symm(name const & relname, expr const & H) {
    return m_ptr->mk_symm(relname, H);
}

optional<expr> app_builder::mk_eq_symm(expr const & H) {
    return m_ptr->mk_eq_symm(H);
}

optional<expr> app_builder::mk_iff_symm(expr const & H) {
    return m_ptr->mk_iff_symm(H);
}

optional<expr> app_builder::mk_trans(name const & relname, expr const & H1, expr const & H2) {
    return m_ptr->mk_trans(relname, H1, H2);
}

optional<expr> app_builder::mk_eq_trans(expr const & H1, expr const & H2) {
    return m_ptr->mk_eq_trans(H1, H2);
}

optional<expr> app_builder::mk_iff_trans(expr const & H1, expr const & H2) {
    return m_ptr->mk_iff_trans(H1, H2);
}

optional<expr> app_builder::mk_eq_rec(expr const & C, expr const & H1, expr const & H2) {
    return m_ptr->mk_eq_rec(C, H1, H2);
}

optional<expr> app_builder::mk_eq_drec(expr const & C, expr const & H1, expr const & H2) {
    return m_ptr->mk_eq_drec(C, H1, H2);
}

void app_builder::set_local_instances(list<expr> const & insts) {
    m_ptr->m_ctx->set_local_instances(insts);
}
}

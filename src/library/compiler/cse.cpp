/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include "runtime/flet.h"
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/expr_maps.h"
#include "kernel/expr_sets.h"
#include "library/compiler/util.h"

namespace lean {
static name * g_cse_fresh = nullptr;

class cse_fn {
    environment       m_env;
    name_generator    m_ngen;
    bool              m_before_erasure;
    expr_map<expr>    m_map;
    std::vector<expr> m_keys;

public:
    expr mk_key(expr const & type, expr const & val) {
        if (m_before_erasure) {
            return val;
        } else {
            /* After erasure, we should also compare the type. For example, we might have

                  x_1 : uint32 := 0
                  x_2 : uint8  := 0

               which are different at runtime. We might also have

                  x_1 : uint8 := _cnstr.0.0.0
                  x_2 : _obj  := _cnstr.0.0.0

               where x_1 is representing a value of an enumeration type,
               and x_2 list.nil.

               We encode the pair using an application.
               This solution is a bit hackish, and we should try to refine it in the future. */
            return mk_app(type, val);
        }
    }

    bool has_never_extract(expr const & e) {
        expr const & fn = get_app_fn(e);
        return is_constant(fn) && has_never_extract_attribute(m_env, const_name(fn));
    }

    expr visit_let(expr e) {
        unsigned keys_size = m_keys.size();
        buffer<expr> fvars;
        buffer<expr> to_keep_fvars;
        buffer<std::tuple<name, expr, expr>> entries;
        while (is_let(e)) {
            expr value = instantiate_rev(let_value(e), fvars.size(), fvars.data());
            expr type  = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            expr key   = mk_key(type, value);
            auto it    = m_map.find(key);
            if (it != m_map.end()) {
                lean_assert(is_fvar(it->second));
                fvars.push_back(it->second);
            } else {
                expr new_value = visit(value);
                expr fvar      = mk_fvar(m_ngen.next());
                fvars.push_back(fvar);
                to_keep_fvars.push_back(fvar);
                entries.emplace_back(let_name(e), type, new_value);
                if (!is_cases_on_app(m_env, new_value) && !has_never_extract(new_value)) {
                    expr new_key = mk_key(type, new_value);
                    m_map.insert(mk_pair(new_key, fvar));
                    m_keys.push_back(new_key);
                }
            }
            e = let_body(e);
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        e = abstract(e, to_keep_fvars.size(), to_keep_fvars.data());
        lean_assert(entries.size() == to_keep_fvars.size());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr new_type  = abstract(std::get<1>(entries[i]), i, to_keep_fvars.data());
            expr new_value = abstract(std::get<2>(entries[i]), i, to_keep_fvars.data());
            e = mk_let(std::get<0>(entries[i]), new_type, new_value, e);
        }
        /* Restore m_map */
        for (unsigned i = keys_size; i < m_keys.size(); i++) {
            m_map.erase(m_keys[i]);
        }
        m_keys.resize(keys_size);
        return e;
    }

    expr visit_lambda(expr e) {
        buffer<expr> fvars;
        buffer<std::tuple<name, expr, binder_info>> entries;
        while (is_lambda(e)) {
            expr domain = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
            expr fvar   = mk_fvar(m_ngen.next());
            entries.emplace_back(binding_name(e), domain, binding_info(e));
            fvars.push_back(fvar);
            e = binding_body(e);
        }
        e = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        e = abstract(e, fvars.size(), fvars.data());
        unsigned i = entries.size();
        while (i > 0) {
            --i;
            expr new_domain = abstract(std::get<1>(entries[i]), i, fvars.data());
            e = mk_lambda(std::get<0>(entries[i]), new_domain, e, std::get<2>(entries[i]));
        }
        return e;
    }

    expr visit_app(expr const & e) {
        if (is_cases_on_app(m_env, e)) {
            buffer<expr> args;
            expr const & c = get_app_args(e, args);
            lean_assert(is_constant(c));
            unsigned minor_idx; unsigned minors_end;
            std::tie(minor_idx, minors_end) = get_cases_on_minors_range(m_env, const_name(c), m_before_erasure);
            for (unsigned i = minor_idx; i < minors_end; i++) {
                args[i] = visit(args[i]);
            }
            return mk_app(c, args);
        } else {
            return e;
        }
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    cse_fn(environment const & env, bool before_erasure):
        m_env(env), m_ngen(*g_cse_fresh), m_before_erasure(before_erasure) {
    }

    expr operator()(expr const & e) { return visit(e); }
};

expr cse_core(environment const & env, expr const & e, bool before_erasure) {
    return cse_fn(env, before_erasure)(e);
}

/* Common case elimination.

   This transformation creates join-points for identical minor premises.
   This is important in code such as
   ```
   def get_fn : expr -> tactic expr
   | (expr.app f _) := pure f
   | _              := throw "expr is not an application"
   ```
   The "else"-branch is duplicated by the equation compiler for each constructor different from `expr.app`. */
class cce_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    buffer<expr>        m_fvars;
    expr_map<bool>      m_cce_candidates;
    buffer<expr>        m_cce_targets;
    name                m_j;
    unsigned            m_next_idx{1};
public:
    environment & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    unsigned get_fvar_idx(expr const & x) {
        return m_lctx.get_local_decl(x).get_idx();
    }

    unsigned get_max_fvar_idx(expr const & e) {
        if (!has_fvar(e))
            return 0;
        unsigned r = 0;
        for_each(e, [&](expr const & x, unsigned) {
                if (!has_fvar(x)) return false;
                if (is_fvar(x)) {
                    unsigned x_idx = get_fvar_idx(x);
                    if (x_idx > r)
                        r = x_idx;
                }
                return true;
            });
        return r;
    }

    expr replace_target(expr const & e, expr const & target, expr const & jmp) {
        return replace(e, [&](expr const & t, unsigned) {
                if (target == t) {
                    return some_expr(jmp);
                }
                return none_expr();
            });
    }

    expr mk_let_lambda(unsigned old_fvars_size, expr body, bool is_let) {
        lean_assert(m_fvars.size() >= old_fvars_size);
        if (m_fvars.size() == old_fvars_size)
            return body;
        unsigned first_var_idx;
        if (old_fvars_size == 0)
            first_var_idx = 0;
        else
            first_var_idx = get_fvar_idx(m_fvars[old_fvars_size]);
        unsigned j = 0;
        buffer<pair<expr, expr>> target_jmp_pairs;
        name_set new_fvar_names;
        for (unsigned i = 0; i < m_cce_targets.size(); i++) {
            expr target = m_cce_targets[i];
            unsigned max_idx    = get_max_fvar_idx(target);
            if (max_idx >= first_var_idx) {
                expr target_type = cheap_beta_reduce(type_checker(m_st, m_lctx).infer(target));
                expr unit        = mk_unit();
                expr unit_mk     = mk_unit_mk();
                expr target_val  = target;
                if (is_lambda(target_val)) {
                    /* Make sure we don't change the arity of the joint point.
                       We use a "trivial let" to encode a joint point that returns a
                       lambda:
                       ```
                          jp : unit -> target_type :=
                          fun _ : unit, let _x : target_type := target_val in _x
                       ```
                    */
                    target_val = ::lean::mk_let("_x", target_type, target_val, mk_bvar(0));
                }
                expr new_val     = ::lean::mk_lambda("u", unit, target_val);
                expr new_type    = ::lean::mk_arrow(unit, target_type);
                expr new_fvar    = m_lctx.mk_local_decl(ngen(), mk_join_point_name(m_j.append_after(m_next_idx)), new_type, new_val);
                new_fvar_names.insert(fvar_name(new_fvar));
                expr jmp         = mk_app(new_fvar, unit_mk);
                if (is_let) {
                    /* We must insert new_fvar after fvar with idx == max_idx */
                    m_next_idx++;
                    unsigned k = old_fvars_size;
                    for (; k < m_fvars.size(); k++) {
                        expr const & fvar = m_fvars[k];
                        if (get_fvar_idx(fvar) > max_idx) {
                            m_fvars.insert(k, new_fvar);
                            /* We need to save the pairs to replace the `target` on let-declarations that occur after k */
                            target_jmp_pairs.emplace_back(target, jmp);
                            break;
                        }
                    }
                    if (k == m_fvars.size()) {
                        m_fvars.push_back(new_fvar);
                    }
                } else {
                    lean_assert(!is_let);
                    /* For lambda we add new free variable after lambda vars */
                    m_fvars.push_back(new_fvar);
                }
                body = replace_target(body, target, jmp);
            } else {
                m_cce_targets[j] = target;
                j++;
            }
        }
        m_cce_targets.shrink(j);
        if (is_let && !target_jmp_pairs.empty()) {
            expr r     = abstract(body, m_fvars.size() - old_fvars_size, m_fvars.data() + old_fvars_size);
            unsigned i = m_fvars.size();
            while (i > old_fvars_size) {
                --i;
                expr fvar       = m_fvars[i];
                local_decl decl = m_lctx.get_local_decl(fvar);
                expr type = abstract(decl.get_type(), i - old_fvars_size, m_fvars.data() + old_fvars_size);
                lean_assert(decl.get_value());
                expr val  = *decl.get_value();
                if ((!new_fvar_names.contains(fvar_name(fvar))) &&
                    (is_lambda(val) || is_cases_on_app(env(), val))) {
                    for (pair<expr, expr> const & p : target_jmp_pairs) {
                        val = replace_target(val, p.first, p.second);
                    }
                }
                val = abstract(val, i - old_fvars_size, m_fvars.data() + old_fvars_size);
                r   = ::lean::mk_let(decl.get_user_name(), type, val, r);
            }
            m_fvars.shrink(old_fvars_size);
            return r;
        } else {
            expr r = m_lctx.mk_lambda(m_fvars.size() - old_fvars_size, m_fvars.data() + old_fvars_size, body);
            m_fvars.shrink(old_fvars_size);
            return r;
        }
    }

    expr mk_let(unsigned old_fvars_size, expr const & body) { return mk_let_lambda(old_fvars_size, body, true); }

    expr mk_lambda(unsigned old_fvars_size, expr const & body) { return mk_let_lambda(old_fvars_size, body, false); }

    expr visit_let(expr e) {
        buffer<expr> let_fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), let_fvars.size(), let_fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), let_fvars.size(), let_fvars.data()));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), new_type, new_val);
            let_fvars.push_back(new_fvar);
            m_fvars.push_back(new_fvar);
            e = let_body(e);
        }
        return instantiate_rev(e, let_fvars.size(), let_fvars.data());
    }

    expr visit_lambda(expr e) {
        lean_assert(is_lambda(e));
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        unsigned fvars_sz1 = m_fvars.size();
        while (is_lambda(e)) {
            /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
            expr new_d    = instantiate_rev(binding_domain(e), m_fvars.size() - fvars_sz1, m_fvars.data() + fvars_sz1);
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_d, binding_info(e));
            m_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        unsigned fvars_sz2 = m_fvars.size();
        expr new_body      = visit(instantiate_rev(e, m_fvars.size() - fvars_sz1, m_fvars.data() + fvars_sz1));
        new_body           = mk_let(fvars_sz2, new_body);
        return mk_lambda(fvars_sz1, new_body);
    }

    void add_candidate(expr const & e) {
        /* TODO(Leo): we should not consider `e` if it is small */
        auto it = m_cce_candidates.find(e);
        if (it == m_cce_candidates.end()) {
            m_cce_candidates.insert(mk_pair(e, true));
        } else if (it->second) {
            m_cce_targets.push_back(e);
            it->second = false;
        }
    }

    expr visit_app(expr const & e) {
        if (!is_cases_on_app(env(), e)) return e;
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        lean_assert(is_constant(c));
        inductive_val I_val      = env().get(const_name(c).get_prefix()).to_inductive_val();
        unsigned motive_idx      = I_val.get_nparams();
        unsigned first_index     = motive_idx + 1;
        unsigned nindices        = I_val.get_nindices();
        unsigned major_idx       = first_index + nindices;
        unsigned first_minor_idx = major_idx + 1;
        unsigned nminors         = length(I_val.get_cnstrs());
        /* visit minor premises */
        for (unsigned i = 0; i < nminors; i++) {
            unsigned minor_idx    = first_minor_idx + i;
            expr minor            = args[minor_idx];
            flet<local_ctx> save_lctx(m_lctx, m_lctx);
            unsigned fvars_sz1 = m_fvars.size();
            while (is_lambda(minor)) {
                expr new_d    = instantiate_rev(binding_domain(minor), m_fvars.size() - fvars_sz1, m_fvars.data() + fvars_sz1);
                expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(minor), new_d, binding_info(minor));
                m_fvars.push_back(new_fvar);
                minor = binding_body(minor);
            }
            bool is_cce_target = !has_loose_bvars(minor);
            unsigned fvars_sz2 = m_fvars.size();
            expr new_minor     = visit(instantiate_rev(minor, m_fvars.size() - fvars_sz1, m_fvars.data() + fvars_sz1));
            new_minor = mk_let(fvars_sz2, new_minor);
            if (is_cce_target && !is_lcnf_atom(new_minor))
                add_candidate(new_minor);
            new_minor = mk_lambda(fvars_sz1, new_minor);
            args[minor_idx] = new_minor;
        }
        return mk_app(c, args);
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    cce_fn(environment const & env, local_ctx const & lctx):
        m_st(env), m_lctx(lctx), m_j("_j") {
    }

    expr operator()(expr const & e) {
        expr r = visit(e);
        return mk_let(0, r);
    }
};

expr cce_core(environment const & env, local_ctx const & lctx, expr const & e) {
    return cce_fn(env, lctx)(e);
}

void initialize_cse() {
    g_cse_fresh = new name("_cse_fresh");
    mark_persistent(g_cse_fresh->raw());
    register_name_generator_prefix(*g_cse_fresh);
}
void finalize_cse() {
    delete g_cse_fresh;
}
}

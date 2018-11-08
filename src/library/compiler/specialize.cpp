/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/class.h"
#include "library/module.h"
#include "library/attribute_manager.h"
#include "library/compiler/util.h"
#include "library/compiler/csimp.h"

#include "library/trace.h"

namespace lean {
bool has_specialize_attribute(environment const & env, name const & n) {
    if (has_attribute(env, "specialize", n))
        return true;
    if (is_internal_name(n) && !n.is_atomic()) {
        /* Auxiliary declarations such as `f._main` are considered to be marked as `@[specialize]`
           if `f` is marked. */
        return has_specialize_attribute(env, n.get_prefix());
    }
    return false;
}

bool has_nospecialize_attribute(environment const & env, name const & n) {
    if (has_attribute(env, "nospecialize", n))
        return true;
    if (is_internal_name(n) && !n.is_atomic()) {
        /* Auxiliary declarations such as `f._main` are considered to be marked as `@[nospecialize]`
           if `f` is marked. */
        return has_nospecialize_attribute(env, n.get_prefix());
    }
    return false;
}

enum class spec_arg_kind { Fixed,
                           FixedNeutral, /* computationally neutral */
                           FixedHO,      /* higher order */
                           FixedInst,    /* type class instance */
                           Other };

static spec_arg_kind to_spec_arg_kind(object_ref const & r) {
    lean_assert(is_scalar(r.raw())); return static_cast<spec_arg_kind>(unbox(r.raw()));
}
typedef objects spec_arg_kinds;
static spec_arg_kinds to_spec_arg_kinds(buffer<spec_arg_kind> const & ks) {
    spec_arg_kinds r;
    unsigned i = ks.size();
    while (i > 0) {
        --i;
        r = spec_arg_kinds(object_ref(box(static_cast<unsigned>(ks[i]))), r);
    }
    return r;
}
static void to_buffer(spec_arg_kinds const & ks, buffer<spec_arg_kind> & r) {
    for (object_ref const & k : ks) {
        r.push_back(to_spec_arg_kind(k));
    }
}

static bool has_fixed_inst_arg(buffer<spec_arg_kind> const & ks) {
    for (spec_arg_kind k : ks) {
        if (k == spec_arg_kind::FixedInst)
            return true;
    }
    return false;
}

/* Return true if `ks` contains kind != Other */
static bool has_kind_ne_other(buffer<spec_arg_kind> const & ks) {
    for (spec_arg_kind k : ks) {
        if (k != spec_arg_kind::Other)
            return true;
    }
    return false;
}

char const * to_str(spec_arg_kind k) {
    switch (k) {
    case spec_arg_kind::Fixed:        return "F";
    case spec_arg_kind::FixedNeutral: return "N";
    case spec_arg_kind::FixedHO:      return "H";
    case spec_arg_kind::FixedInst:    return "I";
    case spec_arg_kind::Other:        return "X";
    }
    lean_unreachable();
}

class spec_info : public object_ref {
    explicit spec_info(b_obj_arg o, bool b):object_ref(o, b) {}
public:
    spec_info(names const & ns, spec_arg_kinds ks):
        object_ref(mk_cnstr(0, ns, ks)) {}
    spec_info():spec_info(names(), spec_arg_kinds()) {}
    spec_info(spec_info const & other):object_ref(other) {}
    spec_info(spec_info && other):object_ref(other) {}
    spec_info & operator=(spec_info const & other) { object_ref::operator=(other); return *this; }
    spec_info & operator=(spec_info && other) { object_ref::operator=(other); return *this; }
    names const & get_mutual_decls() const { return static_cast<names const &>(cnstr_get_ref(*this, 0)); }
    spec_arg_kinds const & get_arg_kinds() const { return static_cast<spec_arg_kinds const &>(cnstr_get_ref(*this, 1)); }
    void serialize(serializer & s) const { s.write_object(raw()); }
    static spec_info deserialize(deserializer & d) { return spec_info(d.read_object(), true); }
};

serializer & operator<<(serializer & s, spec_info const & si) { si.serialize(s); return s; }
deserializer & operator>>(deserializer & d, spec_info & si) { si = spec_info::deserialize(d); return d; }

/* Information for executing code specialization.
   TODO(Leo): use the to be implemented new module system. */
struct specialize_ext : public environment_extension {
    typedef rb_expr_map<name> cache;
    name_map<spec_info> m_spec_info;
    cache               m_cache;
};

struct specialize_ext_reg {
    unsigned m_ext_id;
    specialize_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<specialize_ext>()); }
};

static specialize_ext_reg * g_ext = nullptr;
static specialize_ext const & get_extension(environment const & env) {
    return static_cast<specialize_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, specialize_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<specialize_ext>(ext));
}

/* Support for old module manager.
   Remark: this code will be deleted in the future */
struct spec_info_modification : public modification {
    LEAN_MODIFICATION("speci")

    name      m_name;
    spec_info m_spec_info;

    spec_info_modification(name const & n, spec_info const & s) : m_name(n), m_spec_info(s) {}

    void perform(environment & env) const override {
        specialize_ext ext = get_extension(env);
        ext.m_spec_info.insert(m_name, m_spec_info);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_name << m_spec_info;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name n; spec_info s;
        d >> n >> s;
        return std::make_shared<spec_info_modification>(n, s);
    }
};

typedef buffer<pair<name, buffer<spec_arg_kind>>> spec_info_buffer;

/* We only specialize arguments that are "fixed" in mutual recursive declarations.
   The buffer `info_buffer` stores which arguments are fixed for each declaration in a mutual recursive declaration.
   This procedure traverses `e` and updates `info_buffer`.

   Remark: we only create free variables for the header of each declaration. Then, we assume an argument of a
   recursive call is fixed iff it is a free variable (see `update_spec_info`). */
static void update_info_buffer(environment const & env, expr e, name_set const & S, spec_info_buffer & info_buffer) {
    while (true) {
        switch (e.kind()) {
        case expr_kind::Lambda:
            e = binding_body(e);
            break;
        case expr_kind::Let:
            update_info_buffer(env, let_value(e), S, info_buffer);
            e = let_body(e);
            break;
        case expr_kind::App:
            if (is_cases_on_app(env, e)) {
                buffer<expr> args;
                expr const & c_fn = get_app_args(e, args);
                unsigned minors_begin; unsigned minors_end;
                std::tie(minors_begin, minors_end) = get_cases_on_minors_range(env, const_name(c_fn));
                for (unsigned i = minors_begin; i < minors_end; i++) {
                    update_info_buffer(env, args[i], S, info_buffer);
                }
            } else {
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                if (is_constant(fn) && S.contains(const_name(fn))) {
                    for (auto & entry : info_buffer) {
                        if (entry.first == const_name(fn)) {
                            unsigned sz = entry.second.size();
                            for (unsigned i = 0; i < sz; i++) {
                                if (i >= args.size() || !is_fvar(args[i])) {
                                    entry.second[i] = spec_arg_kind::Other;
                                }
                            }
                            break;
                        }
                    }
                }
            }
            return;
        default:
            return;
        }
    }
}

environment update_spec_info(environment const & env, comp_decls const & ds) {
    name_set S;
    spec_info_buffer d_infos;
    name_generator ngen;
    /* Initialzie d_infos and S */
    for (comp_decl const & d : ds) {
        S.insert(d.fst());
        d_infos.push_back(pair<name, buffer<spec_arg_kind>>());
        auto & info = d_infos.back();
        info.first = d.fst();
        expr code  = d.snd();
        buffer<expr> fvars;
        local_ctx lctx;
        while (is_lambda(code)) {
            expr type = instantiate_rev(binding_domain(code), fvars.size(), fvars.data());
            expr fvar = lctx.mk_local_decl(ngen, binding_name(code), type);
            fvars.push_back(fvar);
            if (is_inst_implicit(binding_info(code))) {
                info.second.push_back(spec_arg_kind::FixedInst);
            } else {
                type_checker tc(env, lctx);
                type = tc.whnf(type);
                if (is_sort(type) || tc.is_prop(type)) {
                    info.second.push_back(spec_arg_kind::FixedNeutral);
                } else if (is_pi(type)) {
                    while (is_pi(type)) {
                        expr fvar = lctx.mk_local_decl(ngen, binding_name(type), binding_domain(type));
                        type = type_checker(env, lctx).whnf(instantiate(binding_body(type), fvar));
                    }
                    if (is_sort(type)) {
                        /* Functions that return types are not relevant */
                        info.second.push_back(spec_arg_kind::FixedNeutral);
                    } else {
                        info.second.push_back(spec_arg_kind::FixedHO);
                    }
                } else {
                    info.second.push_back(spec_arg_kind::Fixed);
                }
            }
            code = binding_body(code);
        }
    }
    /* Update d_infos */
    name x("_x");
    for (comp_decl const & d : ds) {
        buffer<expr> fvars;
        expr code  = d.snd();
        unsigned i = 1;
        /* Create free variables for header variables. */
        while (is_lambda(code)) {
            fvars.push_back(mk_fvar(name(x, i)));
            code = binding_body(code);
        }
        code = instantiate_rev(code, fvars.size(), fvars.data());
        update_info_buffer(env, code, S, d_infos);
    }
    /* Update extension */
    environment new_env = env;
    specialize_ext ext  = get_extension(env);
    names mutual_decls  = map2<name>(ds, [&](comp_decl const & d) { return d.fst(); });
    for (pair<name, buffer<spec_arg_kind>> const & info : d_infos) {
        name const & n = info.first;
        spec_info si(mutual_decls, to_spec_arg_kinds(info.second));
        lean_trace(name({"compiler", "spec_info"}), tout() << n;
                    for (spec_arg_kind k : info.second) {
                        tout() << " " << to_str(k);
                    }
                    tout() << "\n";);
        new_env = module::add(new_env, std::make_shared<spec_info_modification>(n, si));
        ext.m_spec_info.insert(n, si);
    }
    return update(new_env, ext);
}

/* Support for old module manager.
   Remark: this code will be deleted in the future */
struct spec_cache_modification : public modification {
    LEAN_MODIFICATION("specc")

    expr      m_key;
    name      m_fn_name;

    spec_cache_modification(expr const & k, name const & fn) : m_key(k), m_fn_name(fn) {}

    void perform(environment & env) const override {
        specialize_ext ext = get_extension(env);
        ext.m_cache.insert(m_key, m_fn_name);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_key << m_fn_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        expr k; name f;
        d >> k >> f;
        return std::make_shared<spec_cache_modification>(k, f);
    }
};

class specialize_fn {
    type_checker::state m_st;
    csimp_cfg           m_cfg;
    specialize_ext      m_ext;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;
    name                m_at;
    name                m_spec;
    unsigned            m_next_idx{1};

    environment const & env() { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    expr visit_lambda(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_lambda(e)) {
            expr new_type = instantiate_rev(binding_domain(e), fvars.size(), fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_type);
            fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_let(expr e) {
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), fvars.size(), fvars.data()));
            expr new_fvar = m_lctx.mk_local_decl(ngen(), let_name(e), new_type, new_val);
            fvars.push_back(new_fvar);
            e = let_body(e);
        }
        expr r = visit(instantiate_rev(e, fvars.size(), fvars.data()));
        return m_lctx.mk_lambda(fvars, r);
    }

    expr visit_cases_on(expr const & e) {
        lean_assert(is_cases_on_app(env(), e));
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        /* visit minor premises */
        unsigned minor_idx; unsigned minors_end;
        std::tie(minor_idx, minors_end) = get_cases_on_minors_range(env(), const_name(c));
        for (; minor_idx < minors_end; minor_idx++) {
            args[minor_idx] = visit(args[minor_idx]);
        }
        return mk_app(c, args);
    }

    expr find(expr const & e) {
        if (is_fvar(e)) {
            if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
                if (optional<expr> v = decl->get_value()) {
                    return find(*v);
                }
            }
        } else if (is_mdata(e)) {
            return find(mdata_expr(e));
        }
        return e;
    }

    struct spec_ctx {
        typedef rb_expr_map<name> cache;
        names                 m_mutual;
        buffer<expr>          m_params;
        /* `m_vars` contains `m_params` plus all let-declarations.

           Remark: we used to keep m_params and let-declarations in separate buffers.
           This produced incorrect results when the type of a variable in `m_params` depended on a
           let-declaration. */
        buffer<expr>          m_vars;
        cache                 m_cache;
        buffer<comp_decl>     m_pre_decls;

        bool in_mutual_decl(name const & n) const {
            return std::find(m_mutual.begin(), m_mutual.end(), n) != m_mutual.end();
        }
    };

    void get_arg_kinds(name const & fn, buffer<spec_arg_kind> & kinds) {
        spec_info const * info = m_ext.m_spec_info.find(fn);
        lean_assert(info);
        to_buffer(info->get_arg_kinds(), kinds);
    }

    static void to_bool_mask(buffer<spec_arg_kind> const & kinds, bool has_attr, buffer<bool> & mask) {
        unsigned sz     = kinds.size();
        mask.resize(sz, false);
        unsigned i      = sz;
        bool found_inst = false;
        bool first      = true;
        while (i > 0) {
            --i;
            switch (kinds[i]) {
            case spec_arg_kind::Other:
                break;
            case spec_arg_kind::FixedInst:
                mask[i] = true;
                if (first) mask.shrink(i+1);
                first = false;
                found_inst = true;
                break;
            case spec_arg_kind::FixedHO:
            case spec_arg_kind::FixedNeutral:
            case spec_arg_kind::Fixed:
                if (has_attr || found_inst) {
                    mask[i] = true;
                    if (first)
                        mask.shrink(i+1);
                    first = false;
                }
                break;
            }
        }
    }

    void get_bool_mask(name const & fn, buffer<bool> & mask) {
        buffer<spec_arg_kind> kinds;
        get_arg_kinds(fn, kinds);
        to_bool_mask(kinds, has_specialize_attribute(env(), fn), mask);
    }

    name mk_spec_name(name const & fn) {
        name r = fn + m_at + m_base_name + (m_spec.append_after(m_next_idx));
        m_next_idx++;
        return r;
    }

    static expr mk_cache_key(expr const & fn, buffer<optional<expr>> const & mask) {
        expr r = fn;
        for (optional<expr> const & b : mask) {
            if (b)
                r = mk_app(r, *b);
            else
                r = mk_app(r, expr());
        }
        return r;
    }

    bool is_specialize_candidate(expr const & fn, buffer<expr> const & args) {
        lean_assert(is_constant(fn));
        buffer<spec_arg_kind> kinds;
        get_arg_kinds(const_name(fn), kinds);
        if (!has_specialize_attribute(env(), const_name(fn)) && !has_fixed_inst_arg(kinds))
            return false; /* Nothing to specialize */
        if (!has_kind_ne_other(kinds))
            return false; /* Nothing to specialize */
        type_checker tc(m_st, m_lctx);
        for (unsigned i = 0; i < args.size(); i++) {
            if (i >= kinds.size())
                break;
            spec_arg_kind k = kinds[i];
            expr w;
            switch (k) {
            case spec_arg_kind::FixedNeutral:
                break;
            case spec_arg_kind::FixedInst:
                /* We specialize this kind of argument if it reduces to a constructor application or lambda.
                   Type class instances arguments are usually free variables bound to lambda declarations,
                   or quickly reduce to constructor application or lambda. So, the following `whnf` is probably
                   harmless. We need to consider the lambda case because of arguments such as `[decidable_rel lt]` */
                w = tc.whnf(args[i]);
                if (is_constructor_app(env(), w) || is_lambda(w))
                    return true;
                break;
            case spec_arg_kind::FixedHO:
                    /* We specialize higher-order arguments if they are lambda applications or
                       a constant application.

                       Remark: it is not feasible to invoke whnf since it may consume a lot of time. */
                w = find(args[i]);
                if (is_lambda(w) || is_constant(get_app_fn(w)))
                    return true;
                break;
            case spec_arg_kind::Fixed:
                /* We specialize this kind of argument if they are constructor applications or literals.
                   Remark: it is not feasible to invoke whnf since it may consume a lot of time. */
                w = find(args[i]);
                if (is_constructor_app(env(), w) || is_lit(w))
                    return true;
                break;
            case spec_arg_kind::Other:
                break;
            }
        }
        return false;
    }

    void collect_deps(expr e, name_set & collected, spec_ctx & ctx) {
        buffer<expr> todo;
        while (true) {
            for_each(e, [&](expr const & x, unsigned) {
                    if (!has_fvar(x)) return false;
                    if (is_fvar(x) && !collected.contains(fvar_name(x))) {
                        collected.insert(fvar_name(x));
                        local_decl decl = m_lctx.get_local_decl(x);
                        todo.push_back(decl.get_type());
                        if (optional<expr> v = decl.get_value()) {
                            todo.push_back(*v);
                        } else {
                            ctx.m_params.push_back(x);
                        }
                        ctx.m_vars.push_back(x);
                    }
                    return true;
                });
            if (todo.empty())
                return;
            e = todo.back();
            todo.pop_back();
        }
    }

    void sort_fvars(buffer<expr> & fvars) {
        ::lean::sort_fvars(m_lctx, fvars);
    }

    /* Initialize `spec_ctx` fields: `m_vars`. */
    void specialize_init_deps(expr const & fn, buffer<expr> const & args, spec_ctx & ctx) {
        lean_assert(is_constant(fn));
        buffer<spec_arg_kind> kinds;
        get_arg_kinds(const_name(fn), kinds);
        bool has_attr   = has_specialize_attribute(env(), const_name(fn));
        name_set collected;
        unsigned sz     = kinds.size();
        unsigned i      = sz;
        bool found_inst = false;
        while (i > 0) {
            --i;
            switch (kinds[i]) {
            case spec_arg_kind::Other:
                break;
            case spec_arg_kind::FixedInst:
                collect_deps(args[i], collected, ctx);
                found_inst = true;
                break;
            case spec_arg_kind::FixedHO:
            case spec_arg_kind::FixedNeutral:
            case spec_arg_kind::Fixed:
                if (has_attr || found_inst) {
                    collect_deps(args[i], collected, ctx);
                }
                break;
            }
        }
        sort_fvars(ctx.m_vars);
        sort_fvars(ctx.m_params);
        lean_trace(name({"compiler", "spec_candidate"}),
                   tout() << "candidate: " << mk_app(fn, args) << "\nclosure:";
                   for (expr const & p : ctx.m_vars) tout() << " " << p;
                   tout() << "\n";);
    }

    static bool contains(buffer<optional<expr>> const & mask, expr const & e) {
        for (optional<expr> const & o : mask) {
            if (o && *o == e)
                return true;
        }
        return false;
    }

    optional<expr> adjust_rec_apps(expr e, buffer<optional<expr>> const & mask, spec_ctx & ctx) {
        switch (e.kind()) {
        case expr_kind::App:
            if (is_cases_on_app(env(), e)) {
                buffer<expr> args;
                expr const & c = get_app_args(e, args);
                /* visit minor premises */
                unsigned minor_idx; unsigned minors_end;
                std::tie(minor_idx, minors_end) = get_cases_on_minors_range(env(), const_name(c));
                for (; minor_idx < minors_end; minor_idx++) {
                    optional<expr> new_arg = adjust_rec_apps(args[minor_idx], mask, ctx);
                    if (!new_arg) return none_expr();
                    args[minor_idx] = *new_arg;
                }
                return some_expr(mk_app(c, args));
            } else {
                expr const & fn = get_app_fn(e);
                if (!is_constant(fn) || !ctx.in_mutual_decl(const_name(fn)))
                    return some_expr(e);
                buffer<expr> args;
                get_app_args(e, args);
                buffer<bool> bmask;
                get_bool_mask(const_name(fn), bmask);
                lean_assert(bmask.size() <= args.size());
                buffer<optional<expr>> new_mask;
                bool found = false;
                for (unsigned i = 0; i < bmask.size(); i++) {
                    if (bmask[i] && contains(mask, args[i])) {
                        found = true;
                        new_mask.push_back(some_expr(args[i]));
                    } else {
                        new_mask.push_back(none_expr());
                    }
                }
                if (!found)
                    return some_expr(e);
                optional<name> new_fn_name = spec_preprocess(fn, new_mask, ctx);
                if (!new_fn_name) return none_expr();
                expr r = mk_constant(*new_fn_name);
                r = mk_app(r, ctx.m_params);
                for (unsigned i = 0; i < bmask.size(); i++) {
                    if (!bmask[i] || !contains(mask, args[i]))
                        r = mk_app(r, args[i]);
                }
                for (unsigned i = bmask.size(); i < args.size(); i++) {
                    r = mk_app(r, args[i]);
                }
                return some_expr(r);
            }
        case expr_kind::Lambda: {
            buffer<expr> entries;
            while (is_lambda(e)) {
                entries.push_back(e);
                e = binding_body(e);
            }
            optional<expr> new_e = adjust_rec_apps(e, mask, ctx);
            if (!new_e) return none_expr();
            expr r     = *new_e;
            unsigned i = entries.size();
            while (i > 0) {
                --i;
                expr l = entries[i];
                r = mk_lambda(binding_name(l), binding_domain(l), r);
            }
            return some_expr(r);
        }
        case expr_kind::Let: {
            buffer<pair<expr, expr>> entries;
            while (is_let(e)) {
                optional<expr> v = adjust_rec_apps(let_value(e), mask, ctx);
                if (!v) return none_expr();
                expr new_val = *v;
                entries.emplace_back(e, new_val);
                e = let_body(e);
            }
            optional<expr> new_e = adjust_rec_apps(e, mask, ctx);
            if (!new_e) return none_expr();
            expr r     = *new_e;
            unsigned i = entries.size();
            while (i > 0) {
                --i;
                expr l = entries[i].first;
                expr v = entries[i].second;
                r = mk_let(let_name(l), let_type(l), v, r);
            }
            return some_expr(r);
        }
        default:
            return some_expr(e);
        }
    }

    optional<name> spec_preprocess(expr const & fn, buffer<optional<expr>> const & mask, spec_ctx & ctx) {
        lean_assert(is_constant(fn));
        lean_assert(ctx.in_mutual_decl(const_name(fn)));
        expr key = mk_cache_key(fn, mask);
        if (name const * r = ctx.m_cache.find(key)) {
            return optional<name>(*r);
        }
        optional<constant_info> info = env().find(mk_cstage1_name(const_name(fn)));
        if (!info || !info->is_definition()) return optional<name>(); // failed
        name new_name = mk_spec_name(const_name(fn));
        ctx.m_cache.insert(key, new_name);
        expr new_code = instantiate_value_lparams(*info, const_levels(fn));
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> fvars;
        buffer<expr> new_fvars;
        for (optional<expr> const & b : mask) {
            lean_assert(is_lambda(new_code));
            if (b) {
                lean_assert(is_fvar(*b));
                fvars.push_back(*b);
            } else {
                expr type     = instantiate_rev(binding_domain(new_code), fvars.size(), fvars.data());
                expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(new_code), type, binding_info(new_code));
                new_fvars.push_back(new_fvar);
                fvars.push_back(new_fvar);
            }
            new_code = binding_body(new_code);
        }
        new_code = instantiate_rev(new_code, fvars.size(), fvars.data());
        optional<expr> c = adjust_rec_apps(new_code, mask, ctx);
        if (!c) return optional<name>();
        new_code = *c;
        new_code = m_lctx.mk_lambda(new_fvars, new_code);
        ctx.m_pre_decls.push_back(comp_decl(new_name, new_code));
        // lean_trace(name({"compiler", "specialize"}), tout() << "new specialization " << new_name << " :=\n" << new_code << "\n";);
        return optional<name>(new_name);
    }

    expr eta_expand_specialization(expr e) {
        /* Remark: we do not use `type_checker.eta_expand` because it does not preserve LCNF */
        try {
            buffer<expr> args;
            type_checker tc(m_st);
            expr e_type = tc.whnf(tc.infer(e));
            local_ctx lctx;
            while (is_pi(e_type)) {
                expr arg = lctx.mk_local_decl(ngen(), binding_name(e_type), binding_domain(e_type), binding_info(e_type));
                args.push_back(arg);
                e_type = type_checker(m_st, lctx).whnf(instantiate(binding_body(e_type), arg));
            }
            if (args.empty())
                return e;
            buffer<expr> fvars;
            while (is_let(e)) {
                expr type = instantiate_rev(let_type(e), fvars.size(), fvars.data());
                expr val  = instantiate_rev(let_value(e), fvars.size(), fvars.data());
                expr fvar = lctx.mk_local_decl(ngen(), let_name(e), type, val);
                fvars.push_back(fvar);
                e         = let_body(e);
            }
            e = instantiate_rev(e, fvars.size(), fvars.data());
            if (!is_lcnf_atom(e)) {
                e = lctx.mk_local_decl(ngen(), "_e", type_checker(m_st, lctx).infer(e), e);
                fvars.push_back(e);
            }
            e = mk_app(e, args);
            return lctx.mk_lambda(args, lctx.mk_lambda(fvars, e));
        } catch (exception &) {
            /* This can happen since previous compilation steps may have
               produced type incorrect terms. */
            return e;
        }
    }

    void mk_new_decl(comp_decl const & pre_decl, buffer<expr> const & fvars, buffer<expr> const & fvar_vals, spec_ctx & ctx) {
        lean_assert(fvars.size() == fvar_vals.size());
        name n = pre_decl.fst();
        expr code = pre_decl.snd();
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        buffer<expr> new_fvars;
        while (is_lambda(code)) {
            expr type     = instantiate_rev(binding_domain(code), new_fvars.size(), new_fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(code), type, binding_info(code));
            new_fvars.push_back(new_fvar);
            code = binding_body(code);
        }
        code = instantiate_rev(code, new_fvars.size(), new_fvars.data());
        /* Add fvars decls */
        type_checker tc(m_st, m_lctx);
        buffer<expr> new_let_decls;
        name y("_y");
        for (unsigned i = 0; i < fvars.size(); i++) {
            expr type     = tc.infer(fvar_vals[i]);
            expr new_fvar = m_lctx.mk_local_decl(fvar_name(fvars[i]), y.append_after(i+1), type, fvar_vals[i]).mk_ref();
            new_let_decls.push_back(new_fvar);
        }
        code = m_lctx.mk_lambda(new_fvars, code);
        code = m_lctx.mk_lambda(new_let_decls, code);
        code = m_lctx.mk_lambda(ctx.m_vars, code);
        lean_assert(!has_fvar(code));
        /* We add the auxiliary declaration `n` as a "meta" axiom to the environment.
           This is a hack to make sure we can use `csimp` to simplify `code` and
           other definitions that use `n`. `csimp` uses the kernel type checker to infer
           types, and it will fail to infer the type of `n`-applications if we do not have
           an entry in the environment.

           Remark: we mark the axiom as `meta` to make sure it does not polute the environment
           regular definitions.

           We also considered the following cleaner solution: modify `csimp` to use a custom
           type checker that takes the types of auxiliary declarations such as `n` into account.
           A custom type checker would be extra work, but it has other benefits. For example,
           it could have better support for type errors introduced by `csimp`. */
        {
            expr type = cheap_beta_reduce(type_checker(m_st).infer(code));
            declaration aux_ax = mk_axiom(n, names(), type, true /* meta */);
            m_st.env() = module::add(env(), aux_ax, false);
        }
        code = eta_expand_specialization(code);
        code = csimp(env(), code, m_cfg);
        code = visit(code);
        m_new_decls.push_back(comp_decl(n, code));
    }

    optional<expr> get_closed(expr const & e) {
        if (has_univ_param(e)) return none_expr();
        switch (e.kind()) {
        case expr_kind::MVar:  lean_unreachable();
        case expr_kind::Lit:   return some_expr(e);
        case expr_kind::BVar:  return some_expr(e);
        case expr_kind::Sort:  return some_expr(e);
        case expr_kind::Const: return some_expr(e);
        case expr_kind::FVar:
            if (auto v = m_lctx.get_local_decl(e).get_value()) {
                return get_closed(*v);
            } else {
                return none_expr();
            }
        case expr_kind::MData: return get_closed(mdata_expr(e));
        case expr_kind::Proj:  {
            optional<expr> new_s = get_closed(proj_expr(e));
            if (!new_s) return none_expr();
            return some_expr(update_proj(e, *new_s));
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            optional<expr> dom  = get_closed(binding_domain(e));
            if (!dom) return none_expr();
            optional<expr> body = get_closed(binding_body(e));
            if (!body) return none_expr();
            return some_expr(update_binding(e, *dom, *body));
        }
        case expr_kind::App: {
            buffer<expr> args;
            expr const & fn = get_app_args(e, args);
            optional<expr> new_fn = get_closed(fn);
            if (!new_fn) return none_expr();
            for (expr & arg : args) {
                optional<expr> new_arg = get_closed(arg);
                if (!new_arg) return none_expr();
                arg = *new_arg;
            }
            return some_expr(mk_app(*new_fn, args));
        }
        case expr_kind::Let: {
            optional<expr> type  = get_closed(let_type(e));
            if (!type) return none_expr();
            optional<expr> val   = get_closed(let_value(e));
            if (!val) return none_expr();
            optional<expr> body = get_closed(let_body(e));
            if (!body) return none_expr();
            return some_expr(update_let(e, *type, *val, *body));
        }
        }
        lean_unreachable();
    }

    optional<expr> specialize(expr const & fn, buffer<expr> const & args, spec_ctx & ctx) {
        if (!is_specialize_candidate(fn, args))
            return none_expr();
        specialize_init_deps(fn, args, ctx);
        buffer<bool> bmask;
        get_bool_mask(const_name(fn), bmask);
        buffer<optional<expr>> mask;
        buffer<expr> fvars;
        buffer<expr> fvar_vals;
        /* We only try to cache specialization for type class instances.
           For functions marked with the attribute `@[specialize]`, we also specialize other
           fixed arguments (e.g., closures), and most of the time it is not worth to cache the result. */
        bool gcache_enabled = !has_specialize_attribute(env(), const_name(fn));
        buffer<expr> gcache_key_args;
        for (unsigned i = 0; i < bmask.size(); i++) {
            if (bmask[i]) {
                if (gcache_enabled) {
                    if (optional<expr> c = get_closed(args[i])) {
                        gcache_key_args.push_back(*c);
                    } else {
                        /* We only cache specialization results if arguments (expanded by the specializer) are closed. */
                        gcache_enabled = false;
                    }
                }
                name n    = ngen().next();
                expr fvar = mk_fvar(n);
                fvars.push_back(fvar);
                fvar_vals.push_back(args[i]);
                mask.push_back(some_expr(fvar));
            } else {
                mask.push_back(none_expr());
                if (gcache_enabled)
                    gcache_key_args.push_back(expr());
            }
        }
        optional<name> new_fn_name;
        expr key;
        if (gcache_enabled) {
            key = mk_app(fn, gcache_key_args);
            if (name const * it = m_ext.m_cache.find(key))
                new_fn_name = *it;
        }
        if (!new_fn_name) {
            /* Cache does not contain specialization result */
            new_fn_name = spec_preprocess(fn, mask, ctx);
            if (!new_fn_name)
                return none_expr();
            for (comp_decl const & pre_decl : ctx.m_pre_decls) {
                mk_new_decl(pre_decl, fvars, fvar_vals, ctx);
            }
            if (gcache_enabled) {
                m_ext.m_cache.insert(key, *new_fn_name);
                m_st.env() = module::add(env(), std::make_shared<spec_cache_modification>(key, *new_fn_name));
            }
        }
        expr r = mk_constant(*new_fn_name);
        r = mk_app(r, ctx.m_params);
        for (unsigned i = 0; i < bmask.size(); i++) {
            if (!bmask[i])
                r = mk_app(r, args[i]);
        }
        for (unsigned i = bmask.size(); i < args.size(); i++) {
            r = mk_app(r, args[i]);
        }
        return some_expr(r);
    }

    expr visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases_on(e);
        } else {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (!is_constant(fn)
                || has_nospecialize_attribute(env(), const_name(fn))
                || (is_instance(env(), const_name(fn)) && !has_specialize_attribute(env(), const_name(fn)))) {
                return e;
            }
            spec_info const * info = m_ext.m_spec_info.find(const_name(fn));
            if (!info) return e;
            spec_ctx ctx;
            ctx.m_mutual = info->get_mutual_decls();
            if (optional<expr> r = specialize(fn, args, ctx))
                return *r;
            else
                return e;
        }
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::App:    return visit_app(e);
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        default:                return e;
        }
    }

public:
    specialize_fn(environment const & env, csimp_cfg const & cfg):
        m_st(env), m_cfg(cfg), m_ext(get_extension(env)), m_at("_at"), m_spec("_spec") {}

    pair<environment, comp_decls> operator()(comp_decl const & d) {
        m_base_name = d.fst();
        expr new_v = visit(d.snd());
        comp_decl new_d(d.fst(), new_v);
        environment new_env = update(env(), m_ext);
        return mk_pair(new_env, comp_decls(new_d, comp_decls(m_new_decls)));
    }
};

pair<environment, comp_decls> specialize_core(environment const & env, comp_decl const & d, csimp_cfg const & cfg) {
    return specialize_fn(env, cfg)(d);
}

pair<environment, comp_decls> specialize(environment env, comp_decls const & ds, csimp_cfg const & cfg) {
    env = update_spec_info(env, ds);
    comp_decls r;
    for (comp_decl const & d : ds) {
        comp_decls new_ds;
        std::tie(env, new_ds) = specialize_core(env, d, cfg);
        r = append(r, new_ds);
    }
    return mk_pair(env, r);
}

void initialize_specialize() {
    g_ext = new specialize_ext_reg();
    spec_info_modification::init();
    spec_cache_modification::init();
    register_trace_class({"compiler", "spec_info"});
    register_trace_class({"compiler", "spec_candidate"});

    register_system_attribute(basic_attribute::with_check(
            "specialize", "mark definition to always be specialized",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition())
                    throw exception("invalid 'specialize' use, only definitions can be marked as specialize");
            }));

    register_system_attribute(basic_attribute::with_check(
            "nospecialize", "mark definition to never be specialized",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition())
                    throw exception("invalid 'nospecialize' use, only definitions can be marked as nospecialize");
            }));
}

void finalize_specialize() {
    spec_info_modification::finalize();
    spec_cache_modification::finalize();
    delete g_ext;
}
}

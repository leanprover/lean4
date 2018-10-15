/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/instantiate.h"
#include "library/module.h"
#include "library/attribute_manager.h"
#include "library/compiler/util.h"

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

enum class spec_arg_kind { Fixed, FixedInst, Other };
static spec_arg_kind to_spec_arg_kind(object_ref const & r) {
    lean_assert(is_scalar(r)); return static_cast<spec_arg_kind>(unbox(r.raw()));
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
static bool has_fixed_inst_arg(spec_arg_kinds ks) {
    for (object_ref const & k : ks) {
        if (to_spec_arg_kind(k) == spec_arg_kind::FixedInst)
            return true;
    }
    return false;
}

char const * to_str(spec_arg_kind k) {
    switch (k) {
    case spec_arg_kind::Fixed:     return "F";
    case spec_arg_kind::FixedInst: return "I";
    case spec_arg_kind::Other:     return "X";
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
    name_map<spec_info> m_spec_info;
    // TODO(Leo): cache specialization results
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
    /* Initialzie d_infos and S */
    for (comp_decl const & d : ds) {
        S.insert(d.fst());
        d_infos.push_back(pair<name, buffer<spec_arg_kind>>());
        auto & info = d_infos.back();
        info.first = d.fst();
        expr code  = d.snd();
        while (is_lambda(code)) {
            if (is_inst_implicit(binding_info(code)))
                info.second.push_back(spec_arg_kind::FixedInst);
            else
                info.second.push_back(spec_arg_kind::Fixed);
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

class specialize_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    buffer<comp_decl>   m_new_decls;
    name                m_base_name;

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

    expr visit_app(expr const & e) {
        if (is_cases_on_app(env(), e)) {
            return visit_cases_on(e);
        } else {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (!is_constant(fn)) return e;
            specialize_ext ext     = get_extension(env());
            spec_info const * info = ext.m_spec_info.find(const_name(fn));
            if (!info) return e;
            bool has_attr          = has_specialize_attribute(env(), const_name(fn));
            /* If `has_attr` is false, then we specialize if some fixed instance argument reduces
               to a constructor application. Otherwise, we specialize if some fixed argument is
               a lambda or constant application. */
            spec_arg_kinds kinds   = info->get_arg_kinds();
            if (!has_attr && !has_fixed_inst_arg(kinds))
                return e; /* Nothing to specialize */
            type_checker tc(m_st, m_lctx);
            bool is_candidate      = false;
            for (unsigned i = 0; i < args.size(); i++) {
                if (empty(kinds))
                    break;
                spec_arg_kind k = to_spec_arg_kind(head(kinds));
                kinds           = tail(kinds);
                if (!is_lcnf_atom(args[i]))
                    continue; /* In LCNF, non-atomic arguments are computationally irrelevant. */
                expr w;
                switch (k) {
                case spec_arg_kind::Fixed:
                    /* It is not feasible to invoke whnf to `args[i]`
                       since it may consume a lot of time. */
                    w = find(args[i]);
                    if (is_lambda(w) || is_constant(get_app_fn(w)))
                        is_candidate = true;
                    break;
                case spec_arg_kind::FixedInst:
                    /* Type class instances arguments are usually free variables bound to lambda declarations,
                       or quickly reduce to constructor applications. So, the following `whnf` is probably
                       harmless. */
                    w = tc.whnf(args[i]);
                    if (is_constructor_app(env(), w))
                        is_candidate = true;
                    break;
                case spec_arg_kind::Other:
                    break;
                }
                if (is_candidate)
                    break;
            }
            if (!is_candidate)
                return e;
            lean_trace(name({"compiler", "specialize"}), tout() << "candidate: " << e << "\n";);
            // TODO(Leo):
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
    specialize_fn(environment const & env):
        m_st(env) {}

    pair<environment, comp_decls> operator()(comp_decl const & d) {
        m_base_name = d.fst();
        expr new_v = visit(d.snd());
        comp_decl new_d(d.fst(), new_v);
        return mk_pair(m_st.env(), comp_decls(new_d, comp_decls(m_new_decls)));
    }
};

pair<environment, comp_decls> specialize_core(environment const & env, comp_decl const & d) {
    return specialize_fn(env)(d);
}

pair<environment, comp_decls> specialize(environment env, comp_decls const & ds) {
    env = update_spec_info(env, ds);
    comp_decls r;
    for (comp_decl const & d : ds) {
        comp_decls new_ds;
        std::tie(env, new_ds) = specialize_core(env, d);
        r = append(r, new_ds);
    }
    return mk_pair(env, r);
}

void initialize_specialize() {
    g_ext = new specialize_ext_reg();
    spec_info_modification::init();
    register_trace_class({"compiler", "spec_info"});

    register_system_attribute(basic_attribute::with_check(
            "specialize", "mark definition to always be specialized",
            [](environment const & env, name const & d, bool) -> void {
                auto decl = env.get(d);
                if (!decl.is_definition())
                    throw exception("invalid 'specialize' use, only definitions can be marked as specialize");
            }));
}

void finalize_specialize() {
    spec_info_modification::finalize();
    delete g_ext;
}
}

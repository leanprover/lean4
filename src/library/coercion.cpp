/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/rb_map.h"
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "library/coercion.h"
#include "library/module.h"
#include "library/kernel_serializer.h"
#include "library/kernel_bindings.h"

namespace lean {
enum class coercion_class_kind { User, Sort, Fun };

/**
   \brief A coercion is a mapping between classes.
   We support three kinds of classes: User, Sort, Function.
*/
class coercion_class {
    coercion_class_kind m_kind;
    name                m_name; // relevant only if m_kind == User
    coercion_class(coercion_class_kind k, name const & n = name()):m_kind(k), m_name(n) {}
public:
    coercion_class():m_kind(coercion_class_kind::Sort) {}
    static coercion_class mk_user(name n) { return coercion_class(coercion_class_kind::User, n); }
    static coercion_class mk_sort() { return coercion_class(coercion_class_kind::Sort); }
    static coercion_class mk_fun() { return coercion_class(coercion_class_kind::Fun); }
    friend bool operator==(coercion_class const & c1, coercion_class const & c2) { return c1.m_kind == c2.m_kind && c1.m_name == c2.m_name; }
    friend bool operator!=(coercion_class const & c1, coercion_class const & c2) { return !(c1 == c2); }
    coercion_class_kind kind() const { return m_kind; }
    name get_name() const { return m_name; }
};

std::ostream & operator<<(std::ostream & out, coercion_class const & cls) {
    switch (cls.kind()) {
    case coercion_class_kind::User: out << cls.get_name(); break;
    case coercion_class_kind::Sort: out << "Sort-class"; break;
    case coercion_class_kind::Fun:  out << "Function-class"; break;
    }
    return out;
}

struct coercion_class_cmp_fn {
    int operator()(coercion_class const & c1, coercion_class const & c2) const {
        if (c1.kind() != c2.kind())
            return c1.kind() < c2.kind() ? -1 : 1;
        else
            return quick_cmp(c1.get_name(), c2.get_name());
    }
};

struct coercion_info {
    expr              m_fun;
    expr              m_fun_type;
    level_param_names m_level_params;
    unsigned          m_num_args;
    coercion_class    m_to;
    coercion_info() {}
    coercion_info(expr const & f, expr const & f_type, level_param_names const & ls, unsigned num, coercion_class const & cls):
        m_fun(f), m_fun_type(f_type), m_level_params(ls), m_num_args(num), m_to(cls) {}
};

struct coercion_ext : public environment_extension {
    rb_map<name, list<coercion_info>, name_quick_cmp>         m_from;
    rb_map<coercion_class, list<name>, coercion_class_cmp_fn> m_to;
    rb_tree<name, name_quick_cmp>                             m_coercions;
};

struct coercion_ext_reg {
    unsigned m_ext_id;
    coercion_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<coercion_ext>()); }
};

static coercion_ext_reg g_ext;
static coercion_ext const & get_extension(environment const & env) {
    return static_cast<coercion_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, coercion_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<coercion_ext>(ext));
}

// key used for module serialization
static std::string g_coercion_key = "coerce";
static void coercion_reader(deserializer & d, module_idx, shared_environment &,
                            std::function<void(asynch_update_fn const &)> &,
                            std::function<void(delayed_update_fn const &)> & add_delayed_update) {
    name f, C;
    d >> f >> C;
    add_delayed_update([=](environment const & env, io_state const & ios) -> environment {
            return add_coercion(env, f, C, ios);
        });
}
register_module_object_reader_fn g_coercion_reader(g_coercion_key, coercion_reader);

static void check_pi(name const & f, expr const & t) {
    if (!is_pi(t))
        throw exception(sstream() << "invalid coercion, '" << f << "' is not function");
}

/** \brief Return true iff args contains Var(0), Var(1), ..., Var(args.size() - 1) */
static bool check_var_args(buffer<expr> const & args) {
    for (unsigned i = 0; i < args.size(); i++) {
        if (!is_var(args[i]) || var_idx(args[i]) != i)
            return false;
    }
    return true;
}

/** \brief Return true iff param_id(levels[i]) == level_params[i] */
static bool check_levels(levels ls, level_param_names ps) {
    while (!is_nil(ls) && !is_nil(ps)) {
        if (!is_param(head(ls)))
            return false;
        if (param_id(head(ls)) != head(ps))
            return false;
        ls = tail(ls);
        ps = tail(ps);
    }
    return is_nil(ls) && is_nil(ps);
}

optional<coercion_class> type_to_coercion_class(expr const & t) {
    if (is_sort(t)) {
        return optional<coercion_class>(coercion_class::mk_sort());
    } else if (is_pi(t)) {
        return optional<coercion_class>(coercion_class::mk_fun());
    } else {
        expr const & C = get_app_fn(t);
        if (is_constant(C))
            return optional<coercion_class>(coercion_class::mk_user(const_name(C)));
        else
            return optional<coercion_class>();
    }
}

static void add_coercion(coercion_ext & ext, name const & C, expr const & f, expr const & f_type,
                         level_param_names const & ls, unsigned num_args,
                         coercion_class const & cls, io_state const & ios);

static void add_coercion_trans(coercion_ext & ext, io_state const & ios, name const & C,
                               level_param_names const & f_level_params, expr const & f, expr const & f_type, unsigned f_num_args,
                               level_param_names const & g_level_params, expr g, expr const & g_type, unsigned g_num_args) {
    expr t = f_type;
    buffer<expr> args;
    for (unsigned i = 0; i <= f_num_args; i++)
        args.push_back(mk_var(i));
    expr f_app = apply_beta(f, args.size(), args.data());
    buffer<name> f_arg_names;
    buffer<expr> f_arg_types;
    while (is_pi(t)) {
        f_arg_names.push_back(binding_name(t));
        f_arg_types.push_back(binding_domain(t));
        t = binding_body(t);
    }
    expr D_app = t;
    buffer<expr> gf_args;
    gf_args.push_back(f_app);
    expr D_cnst = get_app_rev_args(D_app, gf_args);
    if (gf_args.size() != g_num_args + 1)
        return;
    if (length(const_levels(D_cnst)) != length(g_level_params))
        return;
    // C >-> D >-> E
    g  = instantiate_params(g, g_level_params, const_levels(D_cnst));
    expr gf = apply_beta(g, gf_args.size(), gf_args.data());
    expr gf_type = g_type;
    while (is_pi(gf_type))
        gf_type = binding_body(gf_type);
    coercion_class new_cls = *type_to_coercion_class(gf_type);
    gf_type = instantiate(instantiate_params(gf_type, g_level_params, const_levels(D_cnst)), gf_args.size(), gf_args.data());
    unsigned i = f_arg_types.size();
    while (i > 0) {
        --i;
        gf = mk_lambda(f_arg_names[i], f_arg_types[i], gf);
        gf_type = mk_pi(f_arg_names[i], f_arg_types[i], gf_type);
    }
    add_coercion(ext, C, gf, gf_type, f_level_params, f_num_args, new_cls, ios);
}

static void add_coercion_trans_to(coercion_ext & ext, name const & C, expr const & f, expr const & f_type,
                                  level_param_names const & ls, unsigned num_args,
                                  io_state const & ios) {
    // apply transitivity using ext.m_to
    coercion_class C_cls = coercion_class::mk_user(C);
    auto it1 = ext.m_to.find(C_cls);
    if (!it1)
        return;
    for (name const & B : *it1) {
        auto it2 = ext.m_from.find(B);
        lean_assert(*it2);
        for (coercion_info const & info : *it2) {
            if (info.m_to == C_cls) {
                // B >-> C >-> D
                add_coercion_trans(ext, ios, B,
                                   info.m_level_params, info.m_fun, info.m_fun_type, info.m_num_args,
                                   ls, f, f_type, num_args);
                break;
            }
        }
    }
}

static void add_coercion_trans_from(coercion_ext & ext, name const & C, expr const & f, expr const & f_type,
                                    level_param_names const & ls, unsigned num_args,
                                    coercion_class const & cls, io_state const & ios) {
    // apply transitivity using ext.m_from
    if (cls.kind() != coercion_class_kind::User)
        return; // nothing to do Sort and Fun classes are terminal
    name const & D = cls.get_name();
    auto it = ext.m_from.find(D);
    if (!it)
        return;
    for (coercion_info const & D_info : *it) {
        // C >-> D >-> E
        add_coercion_trans(ext, ios, C,
                           ls, f, f_type, num_args,
                           D_info.m_level_params, D_info.m_fun, D_info.m_fun_type, D_info.m_num_args);
    }
}

// Add entry (D, C) to ext.m_to
static void update_to(coercion_ext & ext, coercion_class const & D, name const & C) {
    auto it = ext.m_to.find(D);
    if (it) {
        ext.m_to.insert(D, list<name>(C, *it));
    } else {
        ext.m_to.insert(D, list<name>(C));
    }
}

static void add_coercion(coercion_ext & ext, name const & C, expr const & f, expr const & f_type,
                         level_param_names const & ls, unsigned num_args,
                         coercion_class const & cls, io_state const & ios) {
    if (cls.kind() == coercion_class_kind::User && C == cls.get_name())
        return;
    auto it = ext.m_from.find(C);
    if (!it) {
        list<coercion_info> infos(coercion_info(f, f_type, ls, num_args, cls));
        ext.m_from.insert(C, infos);
        update_to(ext, cls, C);
    } else {
        list<coercion_info> infos = *it;
        bool found = false;
        for_each(infos, [&](coercion_info const & info) {
                if (info.m_to == cls)
                    ios.get_diagnostic_channel() << "replacing the coercion from '" << C << "' to '" << cls << "'";
                if (is_constant(info.m_fun))
                    ext.m_coercions.erase(const_name(info.m_fun));
                found = true;
            });
        if (found)
            infos = filter(infos, [&](coercion_info const & info) { return info.m_to != cls; });
        infos = list<coercion_info>(coercion_info(f, f_type, ls, num_args, cls), infos);
        ext.m_from.insert(C, infos);
        if (!found)
            update_to(ext, cls, C);
    }
    if (is_constant(f))
        ext.m_coercions.insert(const_name(f));
}

static environment add_coercion(environment env, name const & C, expr const & f, expr const & f_type,
                                level_param_names const & ls, unsigned num_args,
                                coercion_class const & cls, io_state const & ios) {
    coercion_ext ext = get_extension(env);
    add_coercion_trans_to(ext, C, f, f_type, ls, num_args, ios);
    add_coercion_trans_from(ext, C, f, f_type, ls, num_args, cls, ios);
    add_coercion(ext, C, f, f_type, ls, num_args, cls, ios);
    name const & f_name = const_name(f);
    env = add(env, g_coercion_key, [=](serializer & s) {
            s << f_name << C;
        });
    return update(env, ext);
}

environment add_coercion(environment const & env, name const & f, name const & C, io_state const & ios) {
    declaration d = env.get(f);
    unsigned num = 0;
    buffer<expr> args;
    expr t = d.get_type();
    check_pi(f, t);
    while (true) {
        args.clear();
        expr const & C_fn = get_app_rev_args(binding_domain(t), args);
        if (is_constant(C_fn) &&
            const_name(C_fn) == C &&
            num == args.size() &&
            check_var_args(args) &&
            check_levels(const_levels(C_fn), d.get_params())) {
            expr fn = mk_constant(f, const_levels(C_fn));
            optional<coercion_class> cls = type_to_coercion_class(binding_body(t));
            if (!cls)
                throw exception(sstream() << "invalid coercion, '" << f << "' does not have the expected type to be used as a coercion");
            else if (cls->kind() == coercion_class_kind::User && cls->get_name() == C)
                throw exception(sstream() << "invalid coercion, '" << f << "' is a coercion from '" << C << "' on itself");
            return add_coercion(env, C, fn, d.get_type(), d.get_params(), num, *cls, ios);
        }
        t = binding_body(t);
        num++;
        check_pi(f, t);
    }
}

environment add_coercion(environment const & env, name const & f, io_state const & ios) {
    declaration d = env.get(f);
    expr t = d.get_type();
    check_pi(f, t);
    while (is_pi(binding_body(t)))
        t = binding_body(t);
    expr C = get_app_fn(binding_domain(t));
    if (!is_constant(C))
        throw exception(sstream() << "invalid coercion, '" << f << "' does not have the expected type to be used as a coercion");
    return add_coercion(env, f, const_name(C), ios);
}

bool is_coercion(environment const & env, expr const & f) {
    if (is_constant(f)) {
        coercion_ext const & ext = get_extension(env);
        return ext.m_coercions.contains(const_name(f));
    } else {
        return false;
    }
}

bool has_coercions_from(environment const & env, name const & C) {
    coercion_ext const & ext = get_extension(env);
    return ext.m_from.contains(C);
}

bool has_coercions_from(environment const & env, expr const & C) {
    expr const & C_fn = get_app_fn(C);
    if (!is_constant(C_fn))
        return false;
    coercion_ext const & ext = get_extension(env);
    auto it = ext.m_from.find(const_name(C_fn));
    if (!it)
        return false;
    list<coercion_info> const & cs = *it;
    return
        head(cs).m_num_args == get_app_num_args(C) &&
        length(head(cs).m_level_params) == length(const_levels(C_fn));
}

bool has_coercions_to(environment const & env, name const & D) {
    coercion_ext const & ext = get_extension(env);
    return ext.m_to.contains(coercion_class::mk_user(D));
}

bool has_coercions_to(environment const & env, expr const & D) {
    expr const & D_fn = get_app_fn(D);
    return is_constant(D_fn) && has_coercions_to(env, const_name(D_fn));
}

optional<expr> get_coercion(environment const & env, expr const & C, coercion_class const & D) {
    buffer<expr> args;
    expr const & C_fn = get_app_rev_args(C, args);
    if (!is_constant(C_fn))
        return none_expr();
    coercion_ext const & ext = get_extension(env);
    auto it = ext.m_from.find(const_name(C_fn));
    if (!it)
        return none_expr();
    for (coercion_info const & info : *it) {
        if (info.m_to == D && info.m_num_args == args.size() && length(info.m_level_params) == length(const_levels(C_fn))) {
            expr f = instantiate_params(info.m_fun, info.m_level_params, const_levels(C_fn));
            return some_expr(apply_beta(f, args.size(), args.data()));
        }
    }
    return none_expr();
}

optional<expr> get_coercion(environment const & env, expr const & C, name const & D) {
    return get_coercion(env, C, coercion_class::mk_user(D));
}

optional<expr> get_coercion_to_sort(environment const & env, expr const & C) {
    return get_coercion(env, C, coercion_class::mk_sort());
}

optional<expr> get_coercion_to_fun(environment const & env, expr const & C) {
    return get_coercion(env, C, coercion_class::mk_fun());
}

bool get_user_coercions(environment const & env, expr const & C, buffer<std::pair<expr, name>> & result) {
    buffer<expr> args;
    expr const & C_fn = get_app_rev_args(C, args);
    if (!is_constant(C_fn))
        return false;
    coercion_ext const & ext = get_extension(env);
    auto it = ext.m_from.find(const_name(C_fn));
    if (!it)
        return false;
    bool r = false;
    for (coercion_info const & info : *it) {
        if (info.m_to.kind() == coercion_class_kind::User &&
            info.m_num_args == args.size() &&
            length(info.m_level_params) == length(const_levels(C_fn))) {
            expr f = instantiate_params(info.m_fun, info.m_level_params, const_levels(C_fn));
            expr c = apply_beta(f, args.size(), args.data());
            result.emplace_back(c, info.m_to.get_name());
            r = true;
        }
    }
    return r;
}

static int add_coercion(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_environment(L, add_coercion(to_environment(L, 1), to_name_ext(L, 2), get_io_state(L)));
    else if (nargs == 3 && is_io_state(L, 3))
        return push_environment(L, add_coercion(to_environment(L, 1), to_name_ext(L, 2), to_io_state(L, 3)));
    else if (nargs == 3)
        return push_environment(L, add_coercion(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3), get_io_state(L)));
    else
        return push_environment(L, add_coercion(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3), to_io_state(L, 4)));
}
static int is_coercion(lua_State * L) { return push_boolean(L, is_coercion(to_environment(L, 1), to_expr(L, 2))); }
static int has_coercions_from(lua_State * L) {
    if (is_expr(L, 2))
        return push_boolean(L, has_coercions_from(to_environment(L, 1), to_expr(L, 2)));
    else
        return push_boolean(L, has_coercions_from(to_environment(L, 1), to_name_ext(L, 2)));
}
static int has_coercions_to(lua_State * L) {
    if (is_expr(L, 2))
        return push_boolean(L, has_coercions_to(to_environment(L, 1), to_expr(L, 2)));
    else
        return push_boolean(L, has_coercions_to(to_environment(L, 1), to_name_ext(L, 2)));
}
static int get_coercion(lua_State * L) { return push_optional_expr(L, get_coercion(to_environment(L, 1), to_expr(L, 2), to_name_ext(L, 3))); }
static int get_coercion_to_sort(lua_State * L) { return push_optional_expr(L, get_coercion_to_sort(to_environment(L, 1), to_expr(L, 2))); }
static int get_coercion_to_fun(lua_State * L) { return push_optional_expr(L, get_coercion_to_fun(to_environment(L, 1), to_expr(L, 2))); }
static int get_user_coercions(lua_State * L) {
    buffer<std::pair<expr, name>> r;
    get_user_coercions(to_environment(L, 1), to_expr(L, 2), r);
    lua_newtable(L);
    int i = 1;
    for (auto p : r) {
        lua_newtable(L);
        push_expr(L, p.first);
        lua_rawseti(L, -2, 1);
        push_name(L, p.second);
        lua_rawseti(L, -2, 2);
        lua_rawseti(L, -2, i);
        i = i + 1;
    }
    return 1;
}

void open_coercion(lua_State * L) {
    SET_GLOBAL_FUN(add_coercion,         "add_coercion");
    SET_GLOBAL_FUN(is_coercion,          "is_coercion");
    SET_GLOBAL_FUN(has_coercions_from,   "has_coercions_from");
    SET_GLOBAL_FUN(has_coercions_to,     "has_coercions_to");
    SET_GLOBAL_FUN(get_coercion,         "get_coercion");
    SET_GLOBAL_FUN(get_coercion_to_sort, "get_coercion_to_sort");
    SET_GLOBAL_FUN(get_coercion_to_fun,  "get_coercion_to_fun");
    SET_GLOBAL_FUN(get_user_coercions,   "get_user_coercions");
}
}

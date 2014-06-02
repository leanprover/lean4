/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <unordered_set>
#include <vector>
#include <algorithm>
#include "util/list.h"
#include "util/name_map.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/scope.h"
#include "library/module.h"

namespace lean {
namespace scope {
struct level_info {
    unsigned m_pos;   // position inside the section
    level_info(unsigned p = 0):m_pos(p) {}
};

struct decl_info {
    unsigned          m_pos;          // position inside the section
    level_param_names m_level_deps;   // local universe levels this declaration depends on
    levels            m_levels;       // level_param_names ==> levels
    dependencies      m_var_deps;     // local variable/local declarations this declaration depends on
    expr              m_type;         // type of the new declaration
    binder_info       m_binder_info;  // binder information
    bool              m_local;        // true if local

    decl_info():m_pos(0), m_local(true) {}
    decl_info(unsigned pos, level_param_names const & lvl_deps, dependencies const & var_deps, expr const & type,
              binder_info const & bi, bool local):
        m_pos(pos), m_level_deps(lvl_deps), m_var_deps(var_deps), m_type(type), m_binder_info(bi), m_local(local) {
        m_levels = map2<level>(m_level_deps, [](name const & n) { return mk_param_univ(n); });
    }
};

typedef name_map<decl_info>      decl_info_map;
typedef name_map<level_info>     level_info_map;
typedef std::unordered_set<name, name_hash, name_eq> name_hash_set;

class abstraction_context_imp : public abstraction_context {
    unsigned        m_next_local_pos;

    level_info_map  m_levels_info;
    decl_info_map   m_decls_info;

    name_hash_set   m_level_deps;
    name_hash_set   m_var_deps;

public:
    abstraction_context_imp(environment const & env):abstraction_context(env), m_next_local_pos(0) {}

    void clear_deps() {
        m_level_deps.clear();
        m_var_deps.clear();
    }

    // Replace local universe level into parameters.
    virtual level convert(level const & l) {
        return replace(l, [&](level const & l) {
                if (is_global(l)) {
                    auto it = m_levels_info.find(global_id(l));
                    if (it != m_levels_info.end()) {
                        m_level_deps.insert(global_id(l));
                        return optional<level>(mk_param_univ(global_id(l)));
                    }
                }
                return optional<level>();
            });
    }

    // Replace local decls and universe levels with parameters.
    virtual expr convert(expr const & e) {
        return replace(e, [&](expr const & e, unsigned) {
                if (is_constant(e)) {
                    auto it = m_decls_info.find(const_name(e));
                    if (it != m_decls_info.end()) {
                        auto const & info = it->second;
                        for (auto const & d : info.m_level_deps)
                            m_level_deps.insert(d);
                        for (auto const & d : info.m_var_deps)
                            m_var_deps.insert(const_name(d));
                        if (info.m_local) {
                            return some_expr(update_constant(e, levels()));
                        } else {
                            return some_expr(mk_app(update_constant(e, append(const_levels(e), info.m_levels)), info.m_var_deps));
                        }
                    } else {
                        levels new_ls = map(const_levels(e), [&](level const & l) { return convert(l); });
                        return some_expr(update_constant(e, new_ls));
                    }
                } else if (is_sort(e)) {
                    return some_expr(update_sort(e, convert(sort_level(e))));
                } else {
                    return none_expr();
                }
            });
    }

    // Convert m_level_deps into a level_param_names
    virtual level_param_names mk_level_deps() {
        buffer<name> r;
        for (auto d : m_level_deps)
            r.push_back(d);
        std::sort(r.begin(), r.end(), [&](name const & n1, name const & n2) {
                return m_levels_info.find(n1)->second.m_pos < m_levels_info.find(n2)->second.m_pos;
            });
        return to_list(r.begin(), r.end());
    }

    // Convert m_expr_deps into a vector of names
    virtual dependencies mk_var_deps() {
        dependencies r;
        for (auto d : m_var_deps)
            r.push_back(mk_constant(d));
        std::sort(r.begin(), r.end(), [&](expr const & n1, expr const & n2) {
                return m_decls_info.find(const_name(n1))->second.m_pos < m_decls_info.find(const_name(n2))->second.m_pos;
            });
        return r;
    }

    // Create Pi/Lambda(deps, e)
    expr abstract(bool is_lambda, expr e, dependencies const & deps) {
        auto it    = deps.end();
        auto begin = deps.begin();
        while (it != begin) {
            --it;
            auto const & info = m_decls_info.find(const_name(*it))->second;
            if (is_lambda)
                e = ::lean::Fun(*it, info.m_type, e, info.m_binder_info);
            else
                e = ::lean::Pi(*it, info.m_type, e, info.m_binder_info);
        }
        return e;
    }

    // Create Pi(deps, e), the types (and binder_infos) are extracted from m_decls_info
    virtual expr Pi(expr e, dependencies const & deps) {
        return abstract(false, e, deps);
    }

    // Create Lambda(deps, e), the types (and binder_infos) are extracted from m_decls_info
    virtual expr Fun(expr e, dependencies const & deps) {
        return abstract(true, e, deps);
    }

    virtual void add_decl_info(name const & n, level_param_names const & ps, dependencies const & deps, expr const & type) {
        m_decls_info.emplace(n, decl_info(0, ps, deps, type, binder_info(), false));
    }

    void add_global_level(name const & n) {
        m_levels_info.emplace(n, level_info(m_next_local_pos));
        m_next_local_pos++;
    }

    void add_local_decl(declaration const & d, binder_info const & bi) {
        lean_assert(d.is_var_decl());
        lean_assert(is_nil(d.get_params()));
        expr new_type = convert(d.get_type());
        dependencies var_deps = mk_var_deps();
        var_deps.push_back(mk_constant(d.get_name()));
        m_decls_info.emplace(d.get_name(),
                             decl_info(m_next_local_pos, mk_level_deps(), var_deps, new_type, bi, true));
        m_next_local_pos++;
    }

    void add_definition(declaration const & d) {
        lean_assert(d.is_definition());
        expr new_type  = convert(d.get_type());
        expr new_value = convert(d.get_value());
        level_param_names level_deps = mk_level_deps();
        level_param_names new_ls = append(d.get_params(), level_deps);
        dependencies var_deps    = mk_var_deps();
        new_type  = Pi(new_type, var_deps);
        new_value = Fun(new_value, var_deps);
        add_decl_info(d.get_name(), level_deps, var_deps, new_type);
        if (d.is_definition()) {
            declaration new_d = mk_definition(d.get_name(), new_ls, new_type, new_value, d.is_opaque(),
                                              d.get_weight(), d.get_module_idx(), d.use_conv_opt());
            m_env = module::add(m_env, check(m_env, new_d));
        } else {
            declaration new_d = mk_theorem(d.get_name(), new_ls, new_type, new_value);
            m_env = module::add(m_env, check(m_env, new_d));
        }
    }
};

struct scope_ext : public environment_extension {
    struct section {
        environment          m_prev_env;
        list<abstraction_fn> m_fns;
        section(environment const & env):m_prev_env(env) {}
    };
    enum class scope_kind { Namespace, Section };
    list<name>       m_namespaces;
    list<section>    m_sections;
    list<scope_kind> m_scope_kinds;
    scope_ext() {}
};

struct scope_ext_reg {
    unsigned m_ext_id;
    scope_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<scope_ext>()); }
};

static scope_ext_reg g_ext;
static scope_ext const & get_extension(environment const & env) {
    return static_cast<scope_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, scope_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<scope_ext>(ext));
}

environment add(environment const & env, abstraction_fn const & fn) {
    scope_ext ext = get_extension(env);
    if (is_nil(ext.m_sections))
        throw exception("invalid section operation, there is no open scope");
    scope_ext::section s = head(ext.m_sections);
    s.m_fns   = list<abstraction_fn>(fn, s.m_fns);
    ext.m_sections = list<scope_ext::section>(s, tail(ext.m_sections));
    return update(env, ext);
}

environment add_global_level(environment const & env, name const & l) {
    scope_ext const & ext = get_extension(env);
    if (is_nil(ext.m_sections)) {
        return module::add_global_level(env, l);
    } else {
        environment new_env = env.add_global_level(l);
        return add(new_env, [=](abstraction_context & ctx) {
                static_cast<abstraction_context_imp&>(ctx).add_global_level(l);
            });
    }
}

static environment save_section_declaration(environment const & env, declaration const & d, binder_info const & bi) {
    if (d.is_var_decl()) {
        if (!is_nil(d.get_params()))
            throw exception("section parameters and axiom cannot contain universe level parameter");
        return add(env, [=](abstraction_context & ctx) {
                static_cast<abstraction_context_imp&>(ctx).add_local_decl(d, bi);
            });
    } else {
        return add(env, [=](abstraction_context & ctx) {
                static_cast<abstraction_context_imp&>(ctx).add_definition(d);
            });
    }
}

environment add(environment const & env, certified_declaration const & d, binder_info const & bi) {
    scope_ext const & ext = get_extension(env);
    if (is_nil(ext.m_sections))
        return module::add(env, d);
    else
        return save_section_declaration(env.add(d), d.get_declaration(), bi);
}

environment add(environment const & env, declaration const & d, binder_info const & bi) {
    scope_ext const & ext = get_extension(env);
    if (is_nil(ext.m_sections))
        return module::add(env, d);
    else
        return save_section_declaration(env.add(d), d, bi);
}

environment begin_section(environment const & env) {
    scope_ext ext = get_extension(env);
    ext.m_scope_kinds = list<scope_ext::scope_kind>(scope_ext::scope_kind::Section, ext.m_scope_kinds);
    ext.m_sections    = list<scope_ext::section>(scope_ext::section(env), ext.m_sections);
    return update(env, ext);
}

environment begin_namespace(environment const & env, char const * n) {
    scope_ext ext = get_extension(env);
    ext.m_scope_kinds = list<scope_ext::scope_kind>(scope_ext::scope_kind::Namespace, ext.m_scope_kinds);
    ext.m_namespaces  = list<name>(name(get_namespace(env), n), ext.m_namespaces);
    return update(env, ext);
}

environment end(environment const & env) {
    scope_ext ext = get_extension(env);
    if (is_nil(ext.m_scope_kinds))
        throw exception("environment does not have open scopes");
    scope_ext::scope_kind k = head(ext.m_scope_kinds);
    ext.m_scope_kinds = tail(ext.m_scope_kinds);
    switch (k) {
    case scope_ext::scope_kind::Namespace:
        ext.m_namespaces = tail(ext.m_namespaces);
        return update(env, ext);
    case scope_ext::scope_kind::Section: {
        scope_ext::section const & s = head(ext.m_sections);
        environment new_env          = s.m_prev_env;
        buffer<abstraction_fn const *> fns;
        for (auto const & fn : s.m_fns)
            fns.push_back(&fn);
        std::reverse(fns.begin(), fns.end());
        abstraction_context_imp ctx(new_env);
        for (auto p : fns) {
            (*p)(ctx);
            ctx.clear_deps();
        }
        ext.m_sections = tail(ext.m_sections);
        return update(ctx.env(), ext);
    }}
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool has_open_sections(environment const & env) {
    return !is_nil(get_extension(env).m_sections);
}

name const & get_namespace(environment const & env) {
    scope_ext const & ext = get_extension(env);
    if (is_nil(ext.m_namespaces))
        return name::anonymous();
    else
        return head(ext.m_namespaces);
}

optional<declaration> find(environment const & env, name const & n) {
    scope_ext const & ext = get_extension(env);
    for (auto const & p : ext.m_namespaces) {
        name full_name = p + n;
        if (auto d = env.find(full_name)) {
            return d;
        }
    }
    return env.find(n);
}

name get_name_in_namespace(environment const & env, name const & n) {
    if (auto d = env.find(n)) {
        scope_ext const & ext = get_extension(env);
        for (auto const & p : ext.m_namespaces) {
            if (is_prefix_of(p, n)) {
                name r = n.replace_prefix(p, name());
                if (auto d2 = find(env, r)) {
                    if (is_eqp(*d, *d2))
                        return r;
                }
                return n;
            }
        }
    }
    return n;
}
}
}

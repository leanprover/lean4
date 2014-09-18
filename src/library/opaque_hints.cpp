/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"

namespace lean {
struct opaque_hints_ext : public environment_extension {
    name_set m_extra_opaque;
    bool     m_hide_module;
    opaque_hints_ext():m_hide_module(false) {}
};

struct opaque_hints_ext_reg {
    unsigned m_ext_id;
    opaque_hints_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<opaque_hints_ext>()); }
};
static opaque_hints_ext_reg g_ext;
static opaque_hints_ext const & get_extension(environment const & env) {
    return static_cast<opaque_hints_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, opaque_hints_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<opaque_hints_ext>(ext));
}
static void check_definition(environment const & env, name const & n) {
    declaration d = env.get(n);
    if (!d.is_definition())
        throw exception(sstream() << "invalid opaque/transparent, '" << n << "' is not a definition");
}
environment hide_definition(environment const & env, name const & n) {
    check_definition(env, n);
    auto ext = get_extension(env);
    ext.m_extra_opaque.insert(n);
    return update(env, ext);
}
environment expose_definition(environment const & env, name const & n) {
    check_definition(env, n);
    auto ext = get_extension(env);
    if (!ext.m_extra_opaque.contains(n))
        throw exception(sstream() << "invalid 'exposing' opaque/transparent, '" << n << "' is not in the 'extra opaque' set");
    ext.m_extra_opaque.erase(n);
    return update(env, ext);
}
environment set_hide_main_opaque(environment const & env, bool f) {
    auto ext = get_extension(env);
    ext.m_hide_module = f;
    return update(env, ext);
}
bool get_hide_main_opaque(environment const & env) {
    return get_extension(env).m_hide_module;
}
std::unique_ptr<type_checker> mk_type_checker_with_hints(environment const & env, name_generator const & ngen,
                                                         bool relax_main_opaque) {
    auto const & ext = get_extension(env);
    name_set extra_opaque = ext.m_extra_opaque;
    extra_opaque_pred pred([=](name const & n) { return extra_opaque.contains(n); });
    return std::unique_ptr<type_checker>(new type_checker(env, ngen, mk_default_converter(env,
                                                                                          !ext.m_hide_module && relax_main_opaque,
                                                                                          true, pred)));
}
}

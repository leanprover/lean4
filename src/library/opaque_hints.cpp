/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "library/module.h"

namespace lean {
struct opaque_hints_ext : public environment_extension {
    name_set m_opaque;
    name_set m_transparent;
    opaque_hints_ext() {}
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
    ext.m_opaque.insert(n);
    ext.m_transparent.erase(n);
    return update(env, ext);
}
environment expose_definition(environment const & env, name const & n) {
    check_definition(env, n);
    auto ext = get_extension(env);
    ext.m_opaque.erase(n);
    ext.m_transparent.insert(n);
    return update(env, ext);
}
bool is_exposed(environment const & env, name const & n) {
    auto const & ext = get_extension(env);
    return ext.m_transparent.contains(n);
}
std::unique_ptr<type_checker> mk_type_checker_with_hints(environment const & env, name_generator const & ngen,
                                                         bool relax_main_opaque, bool only_main_transparent) {
    auto const & ext = get_extension(env);
    if (only_main_transparent) {
        name_set extra_opaque      = ext.m_opaque;
        name_set extra_transparent = ext.m_transparent;
        extra_opaque_pred pred([=](name const & n) {
                return
                    (!module::is_definition(env, n) || extra_opaque.contains(n)) &&
                    (!extra_transparent.contains(n));
            });
        return std::unique_ptr<type_checker>(new type_checker(env, ngen, mk_default_converter(env, relax_main_opaque,
                                                                                              true, pred)));
    } else {
        name_set extra_opaque = ext.m_opaque;
        extra_opaque_pred pred([=](name const & n) { return extra_opaque.contains(n); });
        return std::unique_ptr<type_checker>(new type_checker(env, ngen, mk_default_converter(env, relax_main_opaque,
                                                                                              true, pred)));
    }
}
}

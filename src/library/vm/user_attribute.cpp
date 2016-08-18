/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <library/tactic/tactic_state.h>
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_string.h"
#include "util/sstream.h"

namespace lean {

static std::string * g_key = nullptr;

struct user_attr_data : public attr_data {
    // to be filled

    void write(serializer &) const {
        lean_unreachable();
    }
    void read(deserializer &) {
        lean_unreachable();
    }
};

class user_attribute : public typed_attribute<user_attr_data> {
public:
    user_attribute(name const & id, char const * descr) : typed_attribute(id, descr) {}
};

struct user_attr_ext : public environment_extension {
    name_map<attribute_ptr> m_attrs;
};

struct user_attr_ext_reg {
    unsigned m_ext_id;
    user_attr_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<user_attr_ext>()); }
};

static user_attr_ext_reg * g_ext = nullptr;
static user_attr_ext const & get_extension(environment const & env) {
    return static_cast<user_attr_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, user_attr_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<user_attr_ext>(ext));
}

static environment add_user_attr(environment const & env, name const & n) {
    if (is_attribute(env, n))
        throw exception(sstream() << "an attribute named [" << n << "] has already been registered");
    auto const & ty = env.get(n).get_type();
    if (!is_constant(ty, get_user_attribute_name()))
        throw exception("invalid attribute.register argument, must be name of a definition of type user_attribute");

    vm_state vm(env);
    vm_obj const & o = vm.invoke(n, {});
    std::string descr = to_string(o);
    user_attr_ext ext = get_extension(env);
    ext.m_attrs.insert(n, attribute_ptr(new user_attribute(n, descr.c_str())));
    return update(env, ext);
}

static void user_attr_reader(deserializer & d, shared_environment & senv,
                             std::function<void(asynch_update_fn const &)> &,
                             std::function<void(delayed_update_fn const &)> &) {
    name n;
    d >> n;
    senv.update([=](environment const & env) -> environment {
        return add_user_attr(env, n);
    });
}

class actual_user_attribute_ext : public user_attribute_ext {
public:
    virtual name_map<attribute_ptr> get_attributes(environment const & env) override {
        return get_extension(env).m_attrs;
    }
};

static vm_obj attribute_get_instances(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    buffer<name> b;
    LEAN_TACTIC_TRY;
    get_attribute(s.env(), n).get_instances(s.env(), b);
    LEAN_TACTIC_CATCH(s);
    return mk_tactic_success(to_obj(b), s);
}

static vm_obj attribute_register(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    LEAN_TACTIC_TRY;
    auto env = add_user_attr(s.env(), n);
    env = module::add(env, *g_key, [=](environment const &, serializer & s) { s << n; });
    return mk_tactic_success(set_env(s, env));
    LEAN_TACTIC_CATCH(s);
}

void initialize_user_attribute() {
    DECLARE_VM_BUILTIN(name({"attribute", "get_instances"}), attribute_get_instances);
    DECLARE_VM_BUILTIN(name({"attribute", "register"}), attribute_register);

    g_ext = new user_attr_ext_reg();
    g_key = new std::string("USR_ATTR");
    register_module_object_reader(*g_key, user_attr_reader);
    set_user_attribute_ext(std::unique_ptr<user_attribute_ext>(new actual_user_attribute_ext));
}
void finalize_user_attribute() {
    delete g_key;
    delete g_ext;
}
}

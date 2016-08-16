/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
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

typedef name_map<attribute_ptr> user_attribute_state;

struct user_attribute_config {
    typedef name entry;
    typedef user_attribute_state state;

    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        if (is_attribute(env, e))
            throw exception(sstream() << "an attribute named [" << e << "] has already been registered");
        auto const & ty = env.get(e).get_type();
        if (!is_constant(ty, get_user_attribute_name()))
            throw exception("malformed [user_attribute] application, definition must be an instance of user_attribute");

        vm_state vm(env);
        vm_decl const & vm_decl = *vm.get_decl(e);
        vm_obj const & o = vm.invoke(e, {});
        std::string descr = to_string(o);
        s.insert(e, attribute_ptr(new user_attribute(e, descr.c_str())));
    }

    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << e;
    }
    static entry read_entry(deserializer & d) {
        name e;
        d >> e;
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.hash());
    }
};

typedef scoped_ext<user_attribute_config> scope_ext;

class actual_user_attribute_ext : public user_attribute_ext {
public:
    virtual name_map<attribute_ptr> get_attributes(environment const & env) override {
        return scope_ext::get_state(env);
    }
};

static vm_obj attribute_get_instances(vm_obj const & vm_env, vm_obj const & vm_n) {
    auto const & env = to_env(vm_env);
    buffer<name> b;
    get_attribute(env, to_name(vm_n)).get_instances(env, b);
    return to_obj(b);
}

void initialize_user_attribute() {
    DECLARE_VM_BUILTIN(name({"attribute", "get_instances"}), attribute_get_instances);

    g_key = new std::string("USR_ATTR");
    scope_ext::initialize();
    register_system_attribute(basic_attribute("user_attribute", "declare user-defined attribute",
                                              [](environment const & env, io_state const & ios, name const & d, unsigned,
                                                 bool persistent) {
                                                  return scope_ext::add_entry(env, ios, d, persistent);
                                              }));
    set_user_attribute_ext(std::unique_ptr<user_attribute_ext>(new actual_user_attribute_ext));
}
void finalize_user_attribute() {
    scope_ext::finalize();
    delete g_key;
}
}

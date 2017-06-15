/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <limits>
#include "util/name_hash_map.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/attribute_manager.h"
#include "library/scoped_ext.h"
#include "library/vm/vm_string.h"
#include "library/tactic/tactic_state.h"

namespace lean {
/* Persisting */
struct hole_command_ext : public environment_extension {
    name_map<pair<name, std::string>> m_cmds;
};

struct hole_command_ext_reg {
    unsigned m_ext_id;
    hole_command_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<hole_command_ext>()); }
};

static hole_command_ext_reg * g_ext = nullptr;
static hole_command_ext const & get_extension(environment const & env) {
    return static_cast<hole_command_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, hole_command_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<hole_command_ext>(ext));
}

static environment add_hole_command(environment const & env, name const & d) {
    auto const & ty = env.get(d).get_type();
    if (!is_constant(ty, get_hole_command_name()))
        throw exception("invalid [hole_command], must be applied to definition of type hole_command");

    vm_state vm(env, options());
    vm_obj o = vm.invoke(d, {});
    name n(to_string(cfield(o, 0)));
    hole_command_ext ext = get_extension(env);
    if (ext.m_cmds.contains(n))
        throw exception(sstream() << "hole commad named [" << n << "] has already been registered");
    std::string descr = to_string(cfield(o, 1));
    ext.m_cmds.insert(n, {d, descr});
    return update(env, ext);
}

struct hole_command_modification : public modification {
    LEAN_MODIFICATION("HOLE_CMD")
    name m_name;

    hole_command_modification() {}
    hole_command_modification(name const & name) : m_name(name) {}

    void perform(environment & env) const override {
        env = add_hole_command(env, m_name);
    }

    void serialize(serializer & s) const override {
        s << m_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<hole_command_modification>(read_name(d));
    }
};

optional<name> is_hole_command(environment const & env, name const & n) {
    if (auto p = get_extension(env).m_cmds.find(n))
        return optional<name>(p->first);
    else
        return optional<name>();
}

void initialize_hole_command() {
    register_system_attribute(basic_attribute(
            "hole_command", "register a definition of type `hole_command` in the system",
            [](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                if (!persistent)
                    throw exception("illegal [hole_command] application, cannot be used locally");
                return module::add_and_perform(env, std::make_shared<hole_command_modification>(n));
            }));
    g_ext = new hole_command_ext_reg();
    hole_command_modification::init();
}
void finalize_hole_command() {
    hole_command_modification::finalize();
    delete g_ext;
}
}

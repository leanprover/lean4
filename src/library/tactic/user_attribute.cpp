/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <limits>
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_string.h"
#include "library/tactic/tactic_state.h"
#include "library/cache_helper.h"
#include "library/trace.h"
#include "util/name_hash_map.h"

namespace lean {

/* typed_attribute */
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

/* Persisting */
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

static environment add_user_attr(environment const & env, name const & d) {
    auto const & ty = env.get(d).get_type();
    if (!is_constant(ty, get_user_attribute_name()) && !is_constant(get_app_fn(ty), get_caching_user_attribute_name()))
        throw exception("invalid attribute.register argument, must be name of a definition of type user_attribute");

    vm_state vm(env, options());
    vm_obj o = vm.invoke(d, {});
    name const & n = to_name(cfield(o, 0));
    if (n.is_anonymous())
        throw exception(sstream() << "invalid attribute.register, anonymous attribute names are not allowed");
    if (is_attribute(env, n))
        throw exception(sstream() << "an attribute named [" << n << "] has already been registered");
    std::string descr = to_string(cfield(o, 1));

    user_attr_ext ext = get_extension(env);
    ext.m_attrs.insert(n, attribute_ptr(new user_attribute(n, descr.c_str())));
    return update(env, ext);
}

/* Integration into attribute_manager */
class actual_user_attribute_ext : public user_attribute_ext {
public:
    virtual name_map<attribute_ptr> get_attributes(environment const & env) override {
        return get_extension(env).m_attrs;
    }
};

struct user_attr_modification : public modification {
    LEAN_MODIFICATION("USR_ATTR")

    name m_name;

    user_attr_modification() {}
    user_attr_modification(name const & name) : m_name(name) {}

    void perform(environment & env) const override {
        env = add_user_attr(env, m_name);
    }

    void serialize(serializer & s) const override {
        s << m_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<user_attr_modification>(read_name(d));
    }
};

/* VM builtins */
vm_obj attribute_get_instances(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    buffer<name> b;
    LEAN_TACTIC_TRY;
    get_attribute(s.env(), n).get_instances(s.env(), b);
    LEAN_TACTIC_CATCH(s);
    return mk_tactic_success(to_obj(b), s);
}

vm_obj attribute_register(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    LEAN_TACTIC_TRY;
    auto env = module::add_and_perform(s.env(), std::make_shared<user_attr_modification>(n));
    return mk_tactic_success(set_env(s, env));
    LEAN_TACTIC_CATCH(s);
}

vm_obj attribute_fingerprint(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    unsigned h;
    LEAN_TACTIC_TRY;
    h = get_attribute(s.env(), n).get_fingerprint(s.env());
    LEAN_TACTIC_CATCH(s);
    return mk_tactic_success(mk_vm_nat(h), s);
}

/* Caching */
struct user_attr_cache {
    struct entry {
        environment    m_env;
        unsigned       m_fingerprint;
        list<unsigned> m_dep_fingerprints;
        vm_obj         m_val;
    };
    name_hash_map<entry> m_cache;
};

MK_THREAD_LOCAL_GET_DEF(user_attr_cache, get_user_attribute_cache);

static bool check_dep_fingerprints(environment const & env, list<name> const & dep_names, list<unsigned> const & dep_fingerprints) {
    if (!dep_names && !dep_fingerprints) {
        return true;
    } else if (dep_names && dep_fingerprints) {
        return
            get_attribute(env, head(dep_names)).get_fingerprint(env) == head(dep_fingerprints) &&
            check_dep_fingerprints(env, tail(dep_names), tail(dep_fingerprints));
    } else {
        return false;
    }
}

vm_obj caching_user_attribute_get_cache(vm_obj const &, vm_obj const & vm_attr, vm_obj const & vm_s) {
    tactic_state const & s       = to_tactic_state(vm_s);
    name const & n               = to_name(cfield(vm_attr, 0));
    vm_obj const & cache_handler = cfield(vm_attr, 2);
    list<name> const & deps      = to_list_name(cfield(vm_attr, 3));
    LEAN_TACTIC_TRY;
    environment const & env = s.env();
    attribute const & attr  = get_attribute(env, n);
    user_attr_cache & cache = get_user_attribute_cache();
    auto it = cache.m_cache.find(attr.get_name());
    if (it != cache.m_cache.end()) {
        if (it->second.m_fingerprint == attr.get_fingerprint(env) &&
            check_dep_fingerprints(env, deps, it->second.m_dep_fingerprints) &&
            env.is_descendant(it->second.m_env)) {
            return mk_tactic_success(it->second.m_val, s);
        }
        lean_trace("user_attributes_cache", tout() << "cached result for [" << attr.get_name() << "] "
                   << "has been found, but cache fingerprint does not match\n";);
    } else {
        lean_trace("user_attributes_cache", tout() << "no cached result for [" << attr.get_name() << "]\n";);
    }
    lean_trace("user_attributes_cache", tout() << "recomputing cache for [" << attr.get_name() << "]\n";);
    buffer<name> instances;
    attr.get_instances(env, instances);
    tactic_state s0 = mk_tactic_state_for(env, options(), {}, local_context(), mk_true());
    vm_obj result = invoke(cache_handler, to_obj(to_list(instances)), to_obj(s0));
    if (is_tactic_success(result) && !get_vm_state().env_was_updated()) {
        user_attr_cache::entry entry;
        entry.m_env         = env;
        entry.m_fingerprint = attr.get_fingerprint(env);
        entry.m_dep_fingerprints = map2<unsigned>(deps, [&](name const & n) {
                return get_attribute(env, n).get_fingerprint(env);
            });
        entry.m_val = cfield(result, 0);
        cache.m_cache.erase(attr.get_name());
        cache.m_cache.insert(mk_pair(attr.get_name(), entry));
        return mk_tactic_success(entry.m_val, s);
    } else {
        return result;
    }
    LEAN_TACTIC_CATCH(s);
}

vm_obj set_basic_attribute_core(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & p, vm_obj const & vm_prio, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    unsigned prio;
    if (is_none(vm_prio))
        prio = LEAN_DEFAULT_PRIORITY;
    else
        prio = force_to_unsigned(get_some_value(vm_prio), std::numeric_limits<unsigned>::max());
    tactic_state const & s = to_tactic_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    if (basic_attribute const * basic_attr = dynamic_cast<basic_attribute const *>(&attr)) {
        bool persistent     = to_bool(p);
        environment new_env = basic_attr->set(s.env(), get_global_ios(), n, prio, persistent);
        return mk_tactic_success(set_env(s, new_env));
    } else {
        return mk_tactic_exception(sstream() << "set_basic_attribute tactic failed, '" << attr_n << "' is not a basic attribute", s);
    }
    LEAN_TACTIC_CATCH(s);
}

vm_obj unset_attribute(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    tactic_state const & s = to_tactic_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    bool persistent        = false;
    environment new_env    = attr.unset(s.env(), get_global_ios(), n, persistent);
    return mk_tactic_success(set_env(s, new_env));
    LEAN_TACTIC_CATCH(s);
}

vm_obj has_attribute(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    tactic_state const & s = to_tactic_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    if (attr.is_instance(s.env(), n)) {
        unsigned prio          = attr.get_prio(s.env(), n);
        return mk_tactic_success(mk_vm_nat(prio), s);
    } else {
        return mk_tactic_exception(sstream() << "'" << n << "' is not tagged with attribute '" << attr_n << "'", s);
    }
    LEAN_TACTIC_CATCH(s);
}

void initialize_user_attribute() {
    DECLARE_VM_BUILTIN(name({"attribute", "get_instances"}),            attribute_get_instances);
    DECLARE_VM_BUILTIN(name({"attribute", "register"}),                 attribute_register);
    DECLARE_VM_BUILTIN(name({"attribute", "fingerprint"}),              attribute_fingerprint);
    DECLARE_VM_BUILTIN(name({"caching_user_attribute", "get_cache"}),   caching_user_attribute_get_cache);
    DECLARE_VM_BUILTIN(name({"tactic",    "set_basic_attribute_core"}), set_basic_attribute_core);
    DECLARE_VM_BUILTIN(name({"tactic",    "unset_attribute"}),          unset_attribute);
    DECLARE_VM_BUILTIN(name({"tactic",    "has_attribute"}),            has_attribute);

    register_trace_class("user_attributes_cache");
    g_ext = new user_attr_ext_reg();
    user_attr_modification::init();
    set_user_attribute_ext(std::unique_ptr<user_attribute_ext>(new actual_user_attribute_ext));
}
void finalize_user_attribute() {
    user_attr_modification::finalize();
    delete g_ext;
}
}

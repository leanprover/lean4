/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <limits>
#include "library/app_builder.h"
#include "library/kernel_serializer.h"
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_parser.h"
#include "library/vm/vm_string.h"
#include "library/cache_helper.h"
#include "library/trace.h"
#include "util/name_hash_map.h"

namespace lean {

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

struct user_attribute_data : public attr_data {
    expr m_param;
    user_attribute_data() {}
    user_attribute_data(expr const & param) : m_param(param) {}

    virtual unsigned hash() const override { return m_param.hash(); }
    void write(serializer & s) const { s << m_param; }
    void read(deserializer & d) { d >> m_param; }
    virtual void print(std::ostream & out) override {
        // TODO(sullrich): use parser-reversing pretty printer as soon as that exists
        if (!is_constant(m_param, get_unit_star_name())) {
            out << " " << m_param;
        }
    }
};

class user_attribute : public typed_attribute<user_attribute_data> {
    name m_decl;
public:
    user_attribute(name const & id, name const & d, char const * descr, after_set_proc const & after_set,
                   before_unset_proc const & before_unset) : typed_attribute(id, descr, after_set, before_unset), m_decl(d) {}

    attr_data_ptr parse_data(abstract_parser & p) const override final {
        lean_assert(dynamic_cast<parser *>(&p));
        auto & p2 = *static_cast<parser *>(&p);
        type_context_old ctx(p2.env(), p2.get_options());
        expr parser = mk_app(ctx, get_user_attribute_parse_reflect_name(), 3, mk_constant(m_decl));
        expr param = to_expr(run_parser(p2, parser));
        return attr_data_ptr(new user_attribute_data(param));
    }
};

vm_obj user_attribute_get_param_untyped(vm_obj const &, vm_obj const &, vm_obj const & vm_attr, vm_obj const & vm_n, vm_obj const & vm_s) {
    name const & attr_n    = to_name(cfield(vm_attr, 0));
    name const & n         = to_name(vm_n);
    tactic_state const & s = tactic::to_state(vm_s);
    LEAN_TACTIC_TRY;
        attribute const & attr = get_attribute(s.env(), attr_n);
        auto uattr = dynamic_cast<user_attribute const *>(&attr);
        lean_always_assert(uattr);
        auto const & data = uattr->get(s.env(), n);
        if (!data) {
            return tactic::mk_exception(sstream() << "failed to retrieve parameter data of attribute '"
                                                  << attr_n << "' on declaration '" << n << "'", s);
        }
        return tactic::mk_success(to_obj(data->m_param), s);
    LEAN_TACTIC_CATCH(s);
}

vm_obj user_attribute_set_untyped(expr const & beta, name const & attr_n, name const & n, expr const & val,
                                        bool persistent, unsigned prio, tactic_state const & s) {
    type_context_old ctx(s.env(), s.get_options());
    if (!ctx.is_def_eq(beta, ctx.infer(val))) {
        return tactic::mk_exception(sstream() << "set_untyped failed, '" << val << "' is not of type '" << beta << "'", s);
    }
    LEAN_TACTIC_TRY;
        attribute const & attr = get_attribute(s.env(), attr_n);
        if (user_attribute const * user_attr = dynamic_cast<user_attribute const *>(&attr)) {
            environment new_env = user_attr->set(s.env(), get_global_ios(), n, prio, user_attribute_data(val), persistent);
            return tactic::mk_success(set_env(s, new_env));
        } else {
            return tactic::mk_exception(sstream() << "set_untyped failed, '" << attr_n << "' is not a user attribute", s);
        }
    LEAN_TACTIC_CATCH(s);
}

vm_obj user_attribute_set_untyped(unsigned DEBUG_CODE(num), vm_obj const * args) {
    lean_assert(num == 9);
    unsigned prio = is_none(args[7]) ? LEAN_DEFAULT_PRIORITY : to_unsigned(get_some_value(args[7]));
    return user_attribute_set_untyped(to_expr(args[2]), to_name(cfield(args[3], 0)), to_name(args[4]),
                                            to_expr(args[5]), to_bool(args[6]), prio, tactic::to_state(args[8]));
}

static environment add_user_attr(environment const & env, name const & d) {
    auto const & ty = env.get(d).get_type();
    if (!is_app_of(ty, get_user_attribute_name(), 2))
        throw exception("invalid [user_attribute] usage, must be applied to definition of type `user_attribute`");

    vm_state vm(env, options());
    vm_obj o = vm.get_constant(d);
    name const & attr_name = to_name(cfield(o, 0));
    if (attr_name.is_anonymous())
        throw exception(sstream() << "invalid user_attribute, anonymous attribute names are not allowed");
    if (is_attribute(env, attr_name))
        throw exception(sstream() << "an attribute named [" << attr_name << "] has already been registered");
    std::string descr = to_string(cfield(o, 1));
    after_set_proc after_set;
    if (!is_none(cfield(o, 2))) {
        after_set = [=](environment const & env, io_state const & ios, name const & n, unsigned prio, bool persistent) {
            vm_state vm(env, ios.get_options());
            scope_vm_state scope(vm);
            vm_obj o = vm.get_constant(d);
            tactic_state s = mk_tactic_state_for(env, options(), {}, local_context(), mk_true());
            auto vm_r = vm.invoke(get_some_value(cfield(o, 2)), to_obj(n), mk_vm_nat(prio), mk_vm_bool(persistent), to_obj(s));
            tactic::report_exception(vm, vm_r);
            return tactic::to_state(tactic::get_success_state(vm_r)).env();
        };
    }
    before_unset_proc before_unset;
    if (!is_none(cfield(o, 3))) {
        before_unset = [=](environment const & env, io_state const & ios, name const & n, bool persistent) {
            vm_state vm(env, ios.get_options());
            scope_vm_state scope(vm);
            vm_obj o = vm.get_constant(d);
            tactic_state s = mk_tactic_state_for(env, options(), {}, local_context(), mk_true());
            auto vm_r = vm.invoke(get_some_value(cfield(o, 3)), to_obj(n), mk_vm_bool(persistent), to_obj(s));
            tactic::report_exception(vm, vm_r);
            return tactic::to_state(tactic::get_success_state(vm_r)).env();
        };
    }

    user_attr_ext ext = get_extension(env);
    ext.m_attrs.insert(attr_name, attribute_ptr(new user_attribute(attr_name, d, descr.c_str(), after_set, before_unset)));
    return update(env, ext);
}

/* Integration into attribute_manager */
class actual_user_attribute_ext : public user_attribute_ext {
public:
    virtual name_map<attribute_ptr> get_attributes(environment const & env) override {
        return get_extension(env).m_attrs;
    }

    void write_entry(serializer & s, attr_data const & data) override {
        lean_assert(dynamic_cast<user_attribute_data const *>(&data));
        static_cast<user_attribute_data const *>(&data)->write(s);
    }

    attr_data_ptr read_entry(deserializer & d) override {
        auto data = new user_attribute_data;
        data->read(d);
        return attr_data_ptr(data);
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
    auto const & s = tactic::to_state(vm_s);
    auto const & n = to_name(vm_n);
    buffer<name> b;
    LEAN_TACTIC_TRY;
    get_attribute(s.env(), n).get_instances(s.env(), b);
    LEAN_TACTIC_CATCH(s);
    return tactic::mk_success(to_obj(b), s);
}

vm_obj attribute_fingerprint(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = tactic::to_state(vm_s);
    auto const & n = to_name(vm_n);
    unsigned h;
    LEAN_TACTIC_TRY;
    h = get_attribute(s.env(), n).get_fingerprint(s.env());
    LEAN_TACTIC_CATCH(s);
    return tactic::mk_success(mk_vm_nat(h), s);
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

/* CACHE_RESET: NO

   This cache contains vm_objects.
*/
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

vm_obj user_attribute_get_cache_core(vm_obj const &, vm_obj const &, vm_obj const & vm_attr, vm_obj const & vm_s) {
    tactic_state const & s       = tactic::to_state(vm_s);
    name const & n               = to_name(cfield(vm_attr, 0));
    vm_obj const & cache_cfg     = cfield(vm_attr, 4);
    vm_obj const & cache_handler = cfield(cache_cfg, 0);
    list<name> const & deps      = to_list_name(cfield(cache_cfg, 1));
    LEAN_TACTIC_TRY;
    environment const & env = s.env();
    attribute const & attr  = get_attribute(env, n);
    user_attr_cache & cache = get_user_attribute_cache();
    auto it = cache.m_cache.find(attr.get_name());
    if (it != cache.m_cache.end()) {
        if (it->second.m_fingerprint == attr.get_fingerprint(env) &&
            check_dep_fingerprints(env, deps, it->second.m_dep_fingerprints) &&
            env.is_descendant(it->second.m_env)) {
            return tactic::mk_success(it->second.m_val, s);
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
    vm_obj result;
    bool was_updated;
    {
        vm_state::reset_env_was_updated_flag scope(get_vm_state());
        result = invoke(cache_handler, to_obj(to_list(instances)), to_obj(s0));
        was_updated = get_vm_state().env_was_updated();
    }
    if (tactic::is_result_success(result)) {
        if (!was_updated) {
            user_attr_cache::entry entry;
            entry.m_env         = env;
            entry.m_fingerprint = attr.get_fingerprint(env);
            entry.m_dep_fingerprints = map2<unsigned>(deps, [&](name const & n) {
                    return get_attribute(env, n).get_fingerprint(env);
                });
            entry.m_val = tactic::get_success_value(result);
            cache.m_cache.erase(attr.get_name());
            cache.m_cache.insert(mk_pair(attr.get_name(), entry));
            return tactic::mk_success(entry.m_val, s);
        } else {
            lean_trace("user_attributes_cache", tout() << "did not cache result for [" << attr.get_name() << "] "
                       "because VM environment has been updated with temporary declarations\n";);
            return tactic::mk_success(tactic::get_success_value(result), s);
        }
    } else {
        return result;
    }
    LEAN_TACTIC_CATCH(s);
}

vm_obj user_attribute_get_cache(vm_state & S, tactic_state const & s, name const & attr_decl_name) {
    vm_obj attr   = S.get_constant(attr_decl_name);
    return user_attribute_get_cache_core(mk_vm_unit(), mk_vm_unit(), attr, to_obj(s));
}

vm_obj set_basic_attribute(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & p, vm_obj const & vm_prio, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    unsigned prio;
    if (is_none(vm_prio))
        prio = LEAN_DEFAULT_PRIORITY;
    else
        prio = force_to_unsigned(get_some_value(vm_prio), std::numeric_limits<unsigned>::max());
    tactic_state const & s = tactic::to_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    if (basic_attribute const * basic_attr = dynamic_cast<basic_attribute const *>(&attr)) {
        bool persistent     = to_bool(p);
        environment new_env = basic_attr->set(s.env(), get_global_ios(), n, prio, persistent);
        return tactic::mk_success(set_env(s, new_env));
    } else {
        return tactic::mk_exception(sstream() << "set_basic_attribute tactic failed, '" << attr_n << "' is not a basic attribute", s);
    }
    LEAN_TACTIC_CATCH(s);
}

vm_obj unset_attribute(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    tactic_state const & s = tactic::to_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    bool persistent        = false;
    environment new_env    = attr.unset(s.env(), get_global_ios(), n, persistent);
    return tactic::mk_success(set_env(s, new_env));
    LEAN_TACTIC_CATCH(s);
}

vm_obj has_attribute(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    tactic_state const & s = tactic::to_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    if (attr.is_instance(s.env(), n)) {
        unsigned prio          = attr.get_prio(s.env(), n);
        return tactic::mk_success(mk_vm_nat(prio), s);
    } else {
        return tactic::mk_exception(sstream() << "'" << n << "' is not tagged with attribute '" << attr_n << "'", s);
    }
    LEAN_TACTIC_CATCH(s);
}

void initialize_user_attribute() {
    DECLARE_VM_BUILTIN(name({"attribute", "get_instances"}),            attribute_get_instances);
    DECLARE_VM_BUILTIN(name({"attribute", "fingerprint"}),              attribute_fingerprint);
    DECLARE_VM_BUILTIN(name({"user_attribute", "get_cache"}),           user_attribute_get_cache_core);
    DECLARE_VM_BUILTIN(name({"user_attribute", "get_param_untyped"}),   user_attribute_get_param_untyped);
    declare_vm_builtin(name({"user_attribute", "set_untyped"}), "user_attribute_set_untyped",
                       9, user_attribute_set_untyped);
    DECLARE_VM_BUILTIN(name({"tactic",    "set_basic_attribute"}),      set_basic_attribute);
    DECLARE_VM_BUILTIN(name({"tactic",    "unset_attribute"}),          unset_attribute);
    DECLARE_VM_BUILTIN(name({"tactic",    "has_attribute"}),            has_attribute);

    register_trace_class("user_attributes_cache");
    register_system_attribute(basic_attribute(
            "user_attribute", "register a definition of type `user_attribute` in the attribute manager",
            [](environment const & env, io_state const &, name const & n, unsigned, bool persistent) {
                if (!persistent)
                    throw exception("illegal [user_attribute] application, cannot be used locally");
                return module::add_and_perform(env, std::make_shared<user_attr_modification>(n));
            }));
    g_ext = new user_attr_ext_reg();
    user_attr_modification::init();
    set_user_attribute_ext(std::unique_ptr<user_attribute_ext>(new actual_user_attribute_ext));
}
void finalize_user_attribute() {
    user_attr_modification::finalize();
    delete g_ext;
}
}

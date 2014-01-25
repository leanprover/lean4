/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <algorithm>
#include "util/list.h"
#include "util/name_set.h"
#include "util/name_map.h"
#include "kernel/environment.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "library/io_state_stream.h"
#include "frontends/lean/frontend.h"

namespace lean {
typedef std::vector<name> dependencies;

struct object_info {
    object       m_object;
    unsigned     m_pos;
    dependencies m_deps;
    expr         m_ref; // a reference to this object, it can be a constant or an application containing the dependencies
    object_info(object const & obj, unsigned pos, dependencies const & deps, expr const & ref):m_object(obj), m_pos(pos), m_deps(deps), m_ref(ref) {}
};

static expr convert(expr const & e, name_map<object_info> & info_map, name_set & dep_set) {
    return replace(e, [&](expr const & e, unsigned) -> expr {
            if (is_constant(e)) {
                auto it = info_map.find(const_name(e));
                if (it != info_map.end()) {
                    auto const & info = it->second;
                    if (info.m_object.is_axiom() || info.m_object.is_var_decl())
                        dep_set.insert(const_name(e));
                    for (auto const & d : info.m_deps)
                        dep_set.insert(d);
                    return info.m_ref;
                }
            }
            return e;
        });
}

static dependencies mk_dependencies(name_map<object_info> & info_map, name_set & dep_set) {
    dependencies r;
    for (auto d : dep_set) r.push_back(d);
    std::sort(r.begin(), r.end(), [&](name const & n1, name const & n2) {
            return info_map.find(n1)->second.m_pos < info_map.find(n2)->second.m_pos;
        });
    return r;
}

static expr mk_ref(object const & obj, dependencies const & deps) {
    if (obj.is_axiom() || obj.is_var_decl()) {
        return mk_constant(obj.get_name());
    } else {
        buffer<expr> args;
        args.push_back(mk_constant(obj.get_name()));
        for (auto d : deps) args.push_back(mk_constant(d));
        if (args.size() == 1)
            return args[0];
        else
            return mk_app(args);
    }
}

static expr abstract(bool is_lambda, expr e, name_map<object_info> & info_map, dependencies const & deps) {
    auto it = deps.end();
    auto begin = deps.begin();
    while (it != begin) {
        --it;
        expr const & type = info_map.find(*it)->second.m_object.get_type();
        if (is_lambda)
            e = Fun(*it, type, e);
        else
            e = Pi(*it, type, e);
    }
    return e;
}

static expr Pi(expr e, name_map<object_info> & info_map, dependencies const & deps) {
    return abstract(false, e, info_map, deps);
}

static expr Fun(expr e, name_map<object_info> & info_map, dependencies const & deps) {
    return abstract(true, e, info_map, deps);
}

std::vector<object> export_local_objects(environment const & env) {
    // TODO(Leo): Revise using Parameters
    if (!env->has_parent())
        return std::vector<object>();
    name_map<object_info> info_map;
    name_set dep_set;
    unsigned pos = 0;
    std::vector<object> new_objects;
    auto it  = env->begin_local_objects();
    auto end = env->end_local_objects();
    for (; it != end; ++it) {
        object const & obj = *it;
        if (!obj.is_axiom() && !obj.is_var_decl() && !obj.is_theorem() && !obj.is_definition())
            continue;
        if (is_explicit(env, obj.get_name()))
            continue;
        dep_set.clear();
        if (obj.is_axiom() || obj.is_var_decl()) {
            expr new_type = convert(obj.get_type(), info_map, dep_set);
            auto new_deps = mk_dependencies(info_map, dep_set);
            info_map.insert(mk_pair(obj.get_name(), object_info(obj, pos, new_deps, mk_ref(obj, new_deps))));
        } else {
            expr new_type = convert(obj.get_type(), info_map, dep_set);
            expr new_val  = convert(obj.get_value(), info_map, dep_set);
            auto new_deps = mk_dependencies(info_map, dep_set);
            new_type = Pi(new_type, info_map, new_deps);
            new_val  = Fun(new_val, info_map, new_deps);
            auto new_obj  = obj.is_theorem() ? mk_theorem(obj.get_name(), new_type, new_val) : mk_definition(obj.get_name(), new_type, new_val, obj.get_weight());
            new_objects.push_back(new_obj);
            info_map.insert(mk_pair(obj.get_name(), object_info(new_obj, pos, new_deps, mk_ref(new_obj, new_deps))));
        }
        pos++;
    }
    return new_objects;
}
}

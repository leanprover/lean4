/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/structure_instance.h"

namespace lean {
static name * g_structure_instance         = nullptr;
static name * g_catchall                   = nullptr;
static name * g_struct                     = nullptr;
static name * g_field                      = nullptr;

static expr mk_structure_instance_core(name const & s, bool ca, names const & fs, unsigned num, expr const * args) {
    kvmap m = set_nat(kvmap(), *g_structure_instance, num);
    m = set_bool(m, *g_catchall, ca);
    m = set_name(m, *g_struct, s);
    expr nil    = mk_Prop();
    expr r      = nil;
    names it_fs = fs;
    for (unsigned i = 0; i < num; i++) {
        name f;
        if (it_fs)
            f = head(it_fs);
        r = mk_app(mk_mdata(set_name(kvmap(), *g_field, f), args[i]), r);
        if (it_fs)
            it_fs = tail(it_fs);
    }
    return mk_mdata(m, r);
}

expr mk_structure_instance(name const & s, buffer<name> const & fns, buffer<expr> const & fvs,
                           buffer<expr> const & sources, bool catchall) {
    lean_assert(fns.size() == fvs.size());
    buffer<expr> aux;
    aux.append(fvs);
    aux.append(sources);
    return mk_structure_instance_core(s, catchall, names(fns), aux.size(), aux.data());
}

expr mk_structure_instance(structure_instance_info const & info) {
    return mk_structure_instance(info.m_struct_name, info.m_field_names, info.m_field_values, info.m_sources,
                                 info.m_catchall);
}

bool is_structure_instance(expr const & e) {
    return is_mdata(e) && get_nat(mdata_data(e), *g_structure_instance);
}

structure_instance_info get_structure_instance_info(expr const & e) {
    lean_assert(is_structure_instance(e));
    structure_instance_info info;
    info.m_struct_name = *get_name(mdata_data(e), *g_struct);
    info.m_catchall    = *get_bool(mdata_data(e), *g_catchall);
    unsigned num = get_nat(mdata_data(e), *g_structure_instance)->get_small_value();
    expr it = mdata_expr(e);
    for (unsigned i = 0; i < num; i++) {
        expr curr  = app_fn(it);
        lean_assert(is_mdata(curr));
        name fname = *get_name(mdata_data(curr), *g_field);
        expr arg   = mdata_expr(curr);
        if (fname.is_anonymous()) {
            info.m_sources.push_back(arg);
        } else {
            info.m_field_names.push_back(fname);
            info.m_field_values.push_back(arg);
        }
        it = app_arg(it);
    }
    std::reverse(info.m_sources.begin(), info.m_sources.end());
    std::reverse(info.m_field_values.begin(), info.m_field_values.end());
    std::reverse(info.m_field_names.begin(), info.m_field_names.end());
    return info;
}

void initialize_structure_instance() {
    g_structure_instance = new name("structure instance");
    g_struct             = new name("struct");
    g_catchall           = new name("catchall");
    g_field              = new name("field");
}

void finalize_structure_instance() {
    delete g_structure_instance;
    delete g_struct;
    delete g_catchall;
    delete g_field;
}
}

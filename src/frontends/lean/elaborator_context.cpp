/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "frontends/lean/elaborator_context.h"

#ifndef LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES
#define LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES true
#endif

#ifndef LEAN_DEFAULT_ELABORATOR_IGNORE_INSTANCES
#define LEAN_DEFAULT_ELABORATOR_IGNORE_INSTANCES false
#endif

namespace lean {
// ==========================================
// elaborator configuration options
static name * g_elaborator_local_instances  = nullptr;
static name * g_elaborator_ignore_instances = nullptr;

name const & get_elaborator_ignore_instances_name() {
    return *g_elaborator_ignore_instances;
}

bool get_elaborator_local_instances(options const & opts) {
    return opts.get_bool(*g_elaborator_local_instances, LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES);
}

bool get_elaborator_ignore_instances(options const & opts) {
    return opts.get_bool(*g_elaborator_ignore_instances, LEAN_DEFAULT_ELABORATOR_IGNORE_INSTANCES);
}
// ==========================================

elaborator_context::elaborator_context(environment const & env, io_state const & ios, local_decls<level> const & lls,
                                       pos_info_provider const * pp, info_manager * info, bool check_unassigned):
    m_env(env), m_ios(ios), m_lls(lls), m_pos_provider(pp), m_info_manager(info), m_check_unassigned(check_unassigned) {
    m_use_local_instances = get_elaborator_local_instances(ios.get_options());
    m_ignore_instances    = get_elaborator_ignore_instances(ios.get_options());
}

void initialize_elaborator_context() {
    g_elaborator_local_instances = new name{"elaborator", "local_instances"};
    g_elaborator_ignore_instances = new name{"elaborator", "ignore_instances"};
    register_bool_option(*g_elaborator_local_instances, LEAN_DEFAULT_ELABORATOR_LOCAL_INSTANCES,
                         "(lean elaborator) use local declarates as class instances");
    register_bool_option(*g_elaborator_ignore_instances, LEAN_DEFAULT_ELABORATOR_IGNORE_INSTANCES,
                         "(lean elaborator) if true, then elaborator does not perform class-instance resolution");
}
void finalize_elaborator_context() {
    delete g_elaborator_local_instances;
    delete g_elaborator_ignore_instances;
}
}

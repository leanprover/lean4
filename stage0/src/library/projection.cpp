/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/inductive.h"
#include "library/util.h"
#include "library/projection.h"

namespace lean {
extern "C" object * lean_mk_projection_info(object * ctor_name, object * nparams, object * i, uint8 from_class);
extern "C" uint8 lean_projection_info_from_class(object * info);

projection_info::projection_info(name const & c, unsigned nparams, unsigned i, bool inst_implicit):
    object_ref(lean_mk_projection_info(c.to_obj_arg(), nat(nparams).to_obj_arg(), nat(i).to_obj_arg(), inst_implicit)) {
}

bool projection_info::is_inst_implicit() const { return lean_projection_info_from_class(to_obj_arg()); }

extern "C" object* lean_add_projection_info(object* env, object* p, object* ctor, object* nparams, object* i, uint8 fromClass);
extern "C" object* lean_get_projection_info(object* env, object* p);

elab_environment save_projection_info(elab_environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i, bool inst_implicit) {
    return elab_environment(lean_add_projection_info(env.to_obj_arg(), p.to_obj_arg(), mk.to_obj_arg(), mk_nat_obj(nparams), mk_nat_obj(i), inst_implicit));
}

optional<projection_info> get_projection_info(elab_environment const & env, name const & p) {
    return to_optional<projection_info>(lean_get_projection_info(env.to_obj_arg(), p.to_obj_arg()));
}
}

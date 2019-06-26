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
projection_info::projection_info(name const & c, unsigned nparams, unsigned i, bool inst_implicit):
    object_ref(mk_cnstr(0, c, nat(nparams), nat(i))) {
    cnstr_set_scalar<unsigned char>(raw(), 3*sizeof(object*), static_cast<unsigned char>(inst_implicit));
}

object* add_projection_info_core(object* env, object* p, object* ctor, object* nparams, object* i, uint8 fromClass);
object* get_projection_info_core(object* env, object* p);

environment save_projection_info(environment const & env, name const & p, name const & mk, unsigned nparams, unsigned i, bool inst_implicit) {
    return environment(add_projection_info_core(env.to_obj_arg(), p.to_obj_arg(), mk.to_obj_arg(), mk_nat_obj(nparams), mk_nat_obj(i), inst_implicit));
}

optional<projection_info> get_projection_info(environment const & env, name const & p) {
    return to_optional<projection_info>(get_projection_info_core(env.to_obj_arg(), p.to_obj_arg()));
}

/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos. */
bool is_structure_like(environment const & env, name const & S) {
    constant_info S_info = env.get(S);
    if (!S_info.is_inductive()) return false;
    inductive_val S_val = S_info.to_inductive_val();
    return length(S_val.get_cnstrs()) == 1 && S_val.get_nindices() == 0;
}
}

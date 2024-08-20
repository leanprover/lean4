/*
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#include "library/elab_environment.h"

namespace lean {
extern "C" obj_res lean_elab_environment_set_base(obj_arg env, obj_arg kenv);
elab_environment elab_environment::add(declaration const & d, bool check) const {
    environment kenv = to_kernel_env().add(d, check);
    return elab_environment(lean_elab_environment_set_base(this->to_obj_arg(), kenv.to_obj_arg()));
}

extern "C" obj_res lean_elab_environment_to_kernel_env(obj_arg);
environment elab_environment::to_kernel_env() const {
    return environment(lean_elab_environment_to_kernel_env(to_obj_arg()));
}

extern "C" obj_res lean_display_stats(obj_arg env, obj_arg w);
void elab_environment::display_stats() const {
    dec_ref(lean_display_stats(to_obj_arg(), io_mk_world()));
}

}

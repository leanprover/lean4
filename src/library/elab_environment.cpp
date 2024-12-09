/*
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#include "runtime/interrupt.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "library/elab_environment.h"
#include "library/compiler/ir_interpreter.h"

namespace lean {
/* Default native reduction function: we use the environment extensions stored in `elab_environment`
   not directly accessible by the type checker in order to run the interpreter (which may then jump
   into native code).

   While more definitions can be added to the kernel environment during type checking, these would
   not yet have any IR, so it is okay to capture and use the `elab_environment` strictly before type
   checking here. */
native_reduce_fn mk_default_native_reduce_fn(elab_environment const & env) {
    return [&env](name const & d) {
        // TODO: we should pass the correct options here in order to respect e.g.
        // `interpreter.prefer_native` during native reduction if we start using it during
        // bootstrapping
        return ir::run_boxed(env, options(), d, 0, nullptr);
    };
}

/* updateBaseAfterKernelAdd (env : Environment) (added : Declaration) (base : Kernel.Environment) :
   Environment

   Updates an elab environment with a given kernel environment after the declaration `d` has been
   added to it. `d` is used to adjust further elab env data such as registering new namespaces.

   NOTE: Ideally this language switching would not be necessary and we could do all this in Lean
   only but the old code generator and `mk_projections` still need a C++ `elab_environment::add`. */
extern "C" obj_res lean_elab_environment_update_base_after_kernel_add(obj_arg env, obj_arg d, obj_arg kenv);

extern "C" obj_res lean_elab_environment_to_kernel_env_no_async(obj_arg);
environment elab_environment::to_kernel_env_no_async() const {
    return environment(lean_elab_environment_to_kernel_env_no_async(to_obj_arg()));
}

elab_environment elab_environment::add(declaration const & d, bool check) const {
    native_reduce_fn red_fn = mk_default_native_reduce_fn(*this);
    environment kenv = to_kernel_env_no_async().add(d, check, &red_fn);
    return elab_environment(lean_elab_environment_update_base_after_kernel_add(this->to_obj_arg(), d.to_obj_arg(), kenv.to_obj_arg()));
}

extern "C" LEAN_EXPORT object * lean_elab_add_decl(object * env, size_t max_heartbeat, object * decl,
    object * opt_cancel_tk) {
    scope_max_heartbeat s(max_heartbeat);
    scope_cancel_tk s2(is_scalar(opt_cancel_tk) ? nullptr : cnstr_get(opt_cancel_tk, 0));
    return catch_kernel_exceptions<elab_environment>([&]() {
            return elab_environment(env).add(declaration(decl, true));
        });
}

extern "C" LEAN_EXPORT object * lean_elab_add_decl_without_checking(object * env, object * decl) {
    return catch_kernel_exceptions<elab_environment>([&]() {
            return elab_environment(env).add(declaration(decl, true), false);
        });
}

extern "C" obj_res lean_elab_environment_to_kernel_env_unchecked(obj_arg);
environment elab_environment::to_kernel_env_unchecked() const {
    return environment(lean_elab_environment_to_kernel_env_unchecked(to_obj_arg()));
}

extern "C" obj_res lean_display_stats(obj_arg env, obj_arg w);
void elab_environment::display_stats() const {
    dec_ref(lean_display_stats(to_obj_arg(), io_mk_world()));
}

extern "C" LEAN_EXPORT lean_object * lean_kernel_is_def_eq(lean_object * obj_env, lean_object * lctx, lean_object * a, lean_object * b) {
    elab_environment env(obj_env);
    native_reduce_fn red_fn = mk_default_native_reduce_fn(env);
    return catch_kernel_exceptions<object*>([&]() {
        return lean_box(type_checker(env.to_kernel_env_unchecked(), local_ctx(lctx), &red_fn).is_def_eq(expr(a), expr(b)));
    });
}

extern "C" LEAN_EXPORT lean_object * lean_kernel_whnf(lean_object * obj_env, lean_object * lctx, lean_object * a) {
    elab_environment env(obj_env);
    native_reduce_fn red_fn = mk_default_native_reduce_fn(env);
    return catch_kernel_exceptions<object*>([&]() {
        return type_checker(env.to_kernel_env_unchecked(), local_ctx(lctx), &red_fn).whnf(expr(a)).steal();
    });
}

extern "C" LEAN_EXPORT lean_object * lean_kernel_check(lean_object * obj_env, lean_object * lctx, lean_object * a) {
    elab_environment env(obj_env);
    native_reduce_fn red_fn = mk_default_native_reduce_fn(env);
    return catch_kernel_exceptions<object*>([&]() {
        return type_checker(environment(env), local_ctx(lctx), &red_fn).check(expr(a)).steal();
    });
}

}

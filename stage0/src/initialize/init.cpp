/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/stackinfo.h"
#include "runtime/thread.h"
#include "runtime/init_module.h"
#include "util/init_module.h"
#include "util/io.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/constructions/init_module.h"
#include "library/print.h"
#include "library/compiler/init_module.h"
#include "initialize/init.h"

namespace lean {
extern "C" object* initialize_Init(uint8_t, object* w);
extern "C" object* initialize_Lean(uint8_t, object* w);

/* Initializes the Lean runtime. Before executing any code which uses the Lean package,
you must first call this function, and then `lean::io_mark_end_initialization`. In between
these two calls, you may also have to run additional initializers for your own modules. */
extern "C" LEAN_EXPORT void lean_initialize() {
    save_stack_info();
    initialize_util_module();
    uint8_t builtin = 1;
    consume_io_result(initialize_Init(builtin, io_mk_world()));
    consume_io_result(initialize_Lean(builtin, io_mk_world()));
    initialize_kernel_module();
    init_default_print_fn();
    initialize_library_core_module();
    initialize_library_module();
    initialize_compiler_module();
    initialize_constructions_module();
}

void finalize() {
    run_thread_finalizers();
    finalize_constructions_module();
    finalize_compiler_module();
    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_util_module();
    run_post_thread_finalizers();
    delete_thread_finalizer_manager();
}

initializer::initializer() {
    lean_initialize();
    /* Remark: We used to call `lean::io_mark_end_initialization` here, however this prevented
    plugins from setting up global state such as environment extensions in their initializers.
    See also `lean_initialize`. */
}

initializer::~initializer() {
    finalize();
}
}

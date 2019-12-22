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
#include "library/tactic/init_module.h"
#include "library/constructions/init_module.h"
#include "library/equations_compiler/init_module.h"
#include "library/print.h"
#include "library/compiler/init_module.h"
#include "frontends/lean/init_module.h"
#include "initialize/init.h"

namespace lean {
extern "C" object* initialize_Init_Default(object* w);
extern "C" object* initialize_Init_Lean(object* w);

extern "C" void lean_initialize() {
    save_stack_info();
    initialize_util_module();
    consume_io_result(initialize_Init_Default(io_mk_world()));
    consume_io_result(initialize_Init_Lean(io_mk_world()));
    initialize_kernel_module();
    init_default_print_fn();
    initialize_library_core_module();
    initialize_library_module();
    initialize_compiler_module();
    initialize_tactic_module();
    initialize_constructions_module();
    initialize_equations_compiler_module();
    initialize_frontend_lean_module();
}

void initialize() {
    lean_initialize();
}

void finalize() {
#ifdef LEAN_TRACK_CUSTOM_ALLOCATORS
    std::cerr << "memory deallocated by memory_pool (before finalization): " << get_memory_deallocated() << "\n";
#endif
#ifdef LEAN_TRACK_LIVE_EXPRS
    std::cerr << "number of live expressions (before finalization): " << get_num_live_exprs() << "\n";
#endif
    run_thread_finalizers();
    finalize_frontend_lean_module();
    finalize_equations_compiler_module();
    finalize_constructions_module();
    finalize_tactic_module();
    finalize_compiler_module();
    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_util_module();
    run_post_thread_finalizers();
#ifdef LEAN_TRACK_CUSTOM_ALLOCATORS
    std::cerr << "memory deallocated by memory_pool (after finalization): " << get_memory_deallocated() << "\n";
#endif
#ifdef LEAN_TRACK_LIVE_EXPRS
    std::cerr << "number of live expressions (after finalization): " << get_num_live_exprs() << "\n";
#endif
    delete_thread_finalizer_manager();
#ifdef LEAN_TRACK_CUSTOM_ALLOCATORS
    std::cerr << "memory deallocated by memory_pool (after thread finalization): " << get_memory_deallocated() << "\n";
#endif
#ifdef LEAN_TRACK_LIVE_EXPRS
    std::cerr << "number of live expressions (after thread finalization): " << get_num_live_exprs() << "\n";
#endif
}

initializer::initializer() {
    initialize();
    lean::io_mark_end_initialization();
}

initializer::~initializer() {
    finalize();
}
}

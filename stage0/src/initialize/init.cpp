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
#include "initialize/init.h"

namespace lean {
extern "C" object* initialize_Init(uint8_t);
extern "C" object* initialize_Std(uint8_t);
extern "C" object* initialize_Lean(uint8_t);
#ifdef LEAN_MINIMAL_CORE_INIT
extern "C" object* initialize_Lean_Compiler_ExportAttr(uint8_t);
extern "C" object* initialize_Lean_Compiler_IR_CompilerM(uint8_t);
extern "C" object* initialize_Lean_Compiler_IR_EmitLLVM(uint8_t);
extern "C" object* initialize_Lean_Compiler_IR_Format(uint8_t);
extern "C" object* initialize_Lean_Compiler_InitAttr(uint8_t);
extern "C" object* initialize_Lean_Compiler_ModPkgExt(uint8_t);
extern "C" object* initialize_Lean_Compiler_NameMangling(uint8_t);
extern "C" object* initialize_Lean_Data_KVMap(uint8_t);
extern "C" object* initialize_Lean_Data_Options(uint8_t);
extern "C" object* initialize_Lean_Declaration(uint8_t);
extern "C" object* initialize_Lean_Environment(uint8_t);
extern "C" object* initialize_Lean_Expr(uint8_t);
extern "C" object* initialize_Lean_Level(uint8_t);
extern "C" object* initialize_Lean_LoadDynlib(uint8_t);
extern "C" object* initialize_Lean_LocalContext(uint8_t);
extern "C" object* initialize_Lean_MetavarContext(uint8_t);
extern "C" object* initialize_Lean_Util_Profile(uint8_t);
extern "C" object* initialize_Lean_Util_Trace(uint8_t);
#endif

static bool g_initialized = false;
/* Initializes the Lean runtime. Before executing any code which uses the Lean package,
you must first call this function, and then `lean::io_mark_end_initialization`. In between
these two calls, you may also have to run additional initializers for your own modules.

This function is, and needs to stay, idempotent; it is called by the generated initializer of every
module using the Lean package, which may happen multiple times in a single executable. */
extern "C" LEAN_EXPORT void lean_initialize() {
    if (g_initialized)
        return;
    g_initialized = true;
    save_stack_info();
    initialize_util_module();
    uint8_t builtin = 1;
    /* The core libs are initialized explicitly because they are referenced other than via `import`:
       C++ calls exported Lean functions, and native code of the current module may be called from a
       previous stage when `prefer_native` is set. Of the three, only `Init` is referenced from C++
       directly (37 symbols across 7 modules); `Std` is referenced by none, and stays for the
       run-time reachability reason below. */
    consume_io_result(initialize_Init(builtin));
    consume_io_result(initialize_Std(builtin));
#ifdef LEAN_MINIMAL_CORE_INIT
    /* Initializing `Lean` initializes every module it transitively imports, which makes the whole
       library reachable from `main` and so keeps it in any statically linked binary: for
       `leanchecker` that is the elaborator, the tactic frameworks and the language server, about
       three quarters of the binary. This lists instead the modules defining the exported Lean
       functions the C++ side calls, i.e. those of `libLean.a` defining a symbol that `libleancpp.a`
       or `libleanrt.a` references but does not define. Regenerate it by taking that difference over
       the object files. Downstream Lean code is unaffected either way: a module's own initializer
       still initializes everything it imports.

       Only sound for a binary that never elaborates Lean source; see `initialize_minimal` in
       `src/initialize/CMakeLists.txt`. */
    consume_io_result(initialize_Lean_Compiler_ExportAttr(builtin));
    consume_io_result(initialize_Lean_Compiler_IR_CompilerM(builtin));
    consume_io_result(initialize_Lean_Compiler_IR_EmitLLVM(builtin));
    consume_io_result(initialize_Lean_Compiler_IR_Format(builtin));
    consume_io_result(initialize_Lean_Compiler_InitAttr(builtin));
    consume_io_result(initialize_Lean_Compiler_ModPkgExt(builtin));
    consume_io_result(initialize_Lean_Compiler_NameMangling(builtin));
    consume_io_result(initialize_Lean_Data_KVMap(builtin));
    consume_io_result(initialize_Lean_Data_Options(builtin));
    consume_io_result(initialize_Lean_Declaration(builtin));
    consume_io_result(initialize_Lean_Environment(builtin));
    consume_io_result(initialize_Lean_Expr(builtin));
    consume_io_result(initialize_Lean_Level(builtin));
    consume_io_result(initialize_Lean_LoadDynlib(builtin));
    consume_io_result(initialize_Lean_LocalContext(builtin));
    consume_io_result(initialize_Lean_MetavarContext(builtin));
    consume_io_result(initialize_Lean_Util_Profile(builtin));
    consume_io_result(initialize_Lean_Util_Trace(builtin));
#else
    /* Initializing `Lean` initializes the whole library, which is critical in two ways that neither
       the import graph nor the C++ call sites make visible.

       It is the pass that registers the builtin elaborators and attributes: those live in leaf
       modules, `Lean.Elab.BuiltinCommand` and friends, which import the framework rather than the
       other way round, so nothing reaches them except this aggregate. Even the `Lean.Elab`
       initializer does not reach all builtins.

       The other exception is modules like `Lean.Meta.ExprDefEq` that are reachable from
       extern-export pairs, which may be called at run time without having the module in the direct
       import closure.

       As almost all binaries shipped with Lean link against `libleanshared`, there is no advantage
       for them of resolving the above issues to allow for leaner linking and so we make an
       exception only for the separately linked, never-elaborating paranoid build as above. */
    consume_io_result(initialize_Lean(builtin));
#endif
    initialize_kernel_module();
    init_default_print_fn();
    initialize_library_core_module();
    initialize_library_module();
    initialize_constructions_module();
}

void finalize() {
    run_thread_finalizers();
    finalize_constructions_module();
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

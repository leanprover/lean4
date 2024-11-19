/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Mac Malone
*/
#include "util/io.h"
#include "util/path.h"
#include "runtime/io.h"
#include "runtime/object.h"
#include "runtime/sstream.h"
#include "runtime/exception.h"
#include "runtime/load_dynlib.h"

#ifdef LEAN_WINDOWS
#include <windows.h>
#else
#include <dlfcn.h>
#endif

namespace lean {
void load_dynlib(std::string path) {
#ifdef LEAN_WINDOWS
    HMODULE h = LoadLibrary(path.c_str());
    if (!h) {
        throw exception(sstream() << "error loading library " << path << ": " << GetLastError());
    }
#else
    void *handle = dlopen(path.c_str(), RTLD_LAZY | RTLD_GLOBAL);
    if (!handle) {
        throw exception(sstream() << "error loading library, " << dlerror());
    }
#endif
    // NOTE: we never unload libraries
}

/* loadDynlib : System.FilePath -> IO Unit */
extern "C" LEAN_EXPORT obj_res lean_load_dynlib(b_obj_arg path, obj_arg) {
    try {
        load_dynlib(string_cstr(path));
        return io_result_mk_ok(box(0));
    } catch (exception & ex) {
        return io_result_mk_error(ex.what());
    }
}

void load_plugin(std::string path) {
    void * init;
    // we never want to look up plugins using the system library search
    path = lrealpath(path);
    std::string pkg = stem(path);
    std::string sym = "initialize_" + pkg;
#ifdef LEAN_WINDOWS
    HMODULE h = LoadLibrary(path.c_str());
    if (!h) {
        throw exception(sstream() << "error loading plugin " << path << ": " << GetLastError());
    }
    init = reinterpret_cast<void *>(GetProcAddress(h, sym.c_str()));
#else
    void *handle = dlopen(path.c_str(), RTLD_LAZY);
    if (!handle) {
        throw exception(sstream() << "error loading plugin, " << dlerror());
    }
    init = dlsym(handle, sym.c_str());
#endif
    if (!init) {
        throw exception(sstream() << "error, plugin " << path << " does not seem to contain a module '" << pkg << "'");
    }
    auto init_fn = reinterpret_cast<object *(*)(uint8_t, object *)>(init);
    object *r = init_fn(1 /* builtin */, io_mk_world());
    consume_io_result(r);
    // NOTE: we never unload plugins
}

/* loadPlugin : System.FilePath -> IO Unit */
extern "C" LEAN_EXPORT obj_res lean_load_plugin(b_obj_arg path, obj_arg) {
    try {
        load_plugin(string_cstr(path));
        return io_result_mk_ok(box(0));
    } catch (exception & ex) {
        return io_result_mk_error(ex.what());
    }
}
}

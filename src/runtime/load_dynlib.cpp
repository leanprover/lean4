/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Mac Malone
*/
#include "util/io.h"
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

/* loadPlugin : System.FilePath -> IO Unit */
extern "C" LEAN_EXPORT obj_res lean_load_plugin(b_obj_arg path, obj_arg) {
    // we never want to look up plugins using the system library search
    std::string rpath;
#if defined(LEAN_EMSCRIPTEN)
    rpath = string_to_std(path);
    auto sep = rpath.rfind('/');
#elif defined(LEAN_WINDOWS)
    constexpr unsigned BufferSize = 8192;
    char buffer[BufferSize];
    DWORD retval = GetFullPathName(string_cstr(path), BufferSize, buffer, nullptr);
    if (retval == 0 || retval > BufferSize) {
        rpath = string_to_std(path);
    } else {
        rpath = std::string(buffer);
    }
    auto sep = rpath.rfind('\\');
#else
    char buffer[PATH_MAX];
    char * tmp = realpath(string_cstr(path), buffer);
    if (tmp) {
        rpath = std::string(tmp);
    } else {
        inc(path);
        return io_result_mk_error(lean_mk_io_error_no_file_or_directory(path, ENOENT, mk_string("")));
    }
    auto sep = rpath.rfind('/');
#endif
    if (sep == std::string::npos) {
        sep = 0;
    } else {
        sep++;
    }
    auto dot = rpath.rfind(".");
    if (dot == std::string::npos) {
        dot = rpath.size();
    }
    std::string pkg = rpath.substr(sep, dot - sep);
    std::string sym = "initialize_" + pkg;
    void * init;
#ifdef LEAN_WINDOWS
    HMODULE h = LoadLibrary(rpath.c_str());
    if (!h) {
        return io_result_mk_error((sstream()
            << "error loading plugin " << rpath << ": " << GetLastError()).str());
    }
    init = reinterpret_cast<void *>(GetProcAddress(h, sym.c_str()));
#else
    // Like lean_load_dynlib, the library is loaded with RTLD_GLOBAL.
    // This ensures the interpreter has access to plugin definitions that are also
    // imported (e.g., an environment extension defined with builtin_initialize).
    // In either case, loading the same symbol twice (and thus e.g. running initializers
    // manipulating global `IO.Ref`s twice) should be avoided; the common module
    // should instead be factored out into a separate shared library
    void *handle = dlopen(rpath.c_str(), RTLD_LAZY | RTLD_GLOBAL);
    if (!handle) {
        return io_result_mk_error((sstream()
            << "error loading plugin, " << dlerror()).str());
    }
    init = dlsym(handle, sym.c_str());
#endif
    if (!init) {
        return io_result_mk_error((sstream()
            << "error, plugin " << rpath << " does not seem to contain a module '" << pkg << "'").str());
    }
    auto init_fn = reinterpret_cast<object *(*)(uint8_t, object *)>(init);
    return init_fn(1 /* builtin */, io_mk_world());
    // NOTE: we never unload plugins
}

void load_plugin(std::string path) {
    consume_io_result(lean_load_plugin(mk_string(path), io_mk_world()));
}
}

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "library/native_compiler/dynamic_library.h"
#include <string>
// Interacting with dynamic linking is *not* cross-platform, this is my first
// attempt at supporting all platforms.
#if !defined (LEAN_WINDOWS) || defined(LEAN_CYGWIN)
#include <dlfcn.h>
#endif
#include "util/exception.h"

namespace lean {
#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
void * dlopen(char const * /* file */, int /* mode */) {
    // TODO(Jared): add windows support
    throw exception("Windows does not currently have support for dynamically loading object files");
}
char const * dlerror() {
    throw exception("Windows does not currently have support for dynamically loading object files");
}
void * dlsym(void *, char const *) {
    throw exception("Windows does not currently have support for dynamically loading object files");
}
int dlclose(void *) { // NOLINT
    throw exception("Windows does not currently have support for dynamically loading object files");
}
#define RTLD_LAZY 0
#define RTLD_GLOBAL 1
#endif

dynamic_library::dynamic_library(std::string library_path):
    m_name(library_path), m_handle(nullptr) {
    m_handle =  dlopen(library_path.c_str(), RTLD_LAZY | RTLD_GLOBAL);

    // Check to see if an error occured while performing dynamic linking.
    if (!m_handle) {
        auto last_error_msg = dlerror();
        throw dynamic_linking_exception(std::string(last_error_msg));
    }
}

dynamic_library::~dynamic_library() {
    dlclose(m_handle);
}

dynamic_symbol dynamic_library::symbol(std::string name) {
    auto sym = dlsym(m_handle, name.c_str());

    if (sym == nullptr) {
        auto last_error_msg = dlerror();
        throw dynamic_linking_exception(std::string(last_error_msg));
    }

    return sym;
}
}

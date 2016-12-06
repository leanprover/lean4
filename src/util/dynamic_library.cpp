/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/

#include <string>

// Interacting with dynamic linking is *not* cross-platform, this is my first
// attempt at supporting all platforms.

#if defined(LEAN_WINDOWS) && !defined(LEAN_CYGWIN)
void dlopen(const char * file, int mode) {
    // TODO: add windows support
    throw std::runtime_error("Windows does not currently have support for dynamically loading object files");
}
#elif defined(__APPLE__)
// OSX version, dlfcn should be availble on this platform
#include <dlfcn.h>
#else
// Linux verison, dlfcn should be availble on this platform
#include <dlfcn.h>
#endif
#include "dynamic_library.h"

namespace lean {


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
    auto err = dlclose(m_handle);
    if (err != 0) {
        auto last_error_msg = dlerror();
        throw dynamic_linking_exception(std::string(last_error_msg));
    }
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

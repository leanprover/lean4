/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include <string>
#include <iostream>
#include "kernel/environment.h"
#include "kernel/expr.h"

namespace lean  {

#define LEAN_STATIC_LIB "leanstatic"
#define LEAN_SHARED_LIB "leanshared"

class cpp_compiler {
    buffer<std::string> m_library_paths;
    buffer<std::string> m_include_paths;
    buffer<std::string> m_files;
    buffer<std::string> m_link;

    bool m_debug;
    bool m_shared;
    bool m_pic;

public:
    cpp_compiler & link(std::string lib);
    cpp_compiler & library_path(std::string lib_path);
    cpp_compiler & include_path(std::string include_path);
    cpp_compiler & debug(bool on);
    cpp_compiler & shared_library(bool on);
    cpp_compiler & pic(bool on);
    cpp_compiler & file(std::string file_path);
    cpp_compiler();
    void run();
};

// Setup a compiler for building executables.
cpp_compiler mk_executable_compiler();

// Setup a compiler for building dynamic libraries.
cpp_compiler mk_shared_compiler();

}

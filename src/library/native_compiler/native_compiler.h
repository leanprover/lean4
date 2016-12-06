/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include "kernel/environment.h"

namespace lean {

void initialize_install_path();
std::string get_install_path();

struct extern_fn {
    bool m_in_lean_namespace;
    name m_name;
    unsigned m_arity;
    extern_fn(bool in_lean_namespace, name n, unsigned arity) :
        m_in_lean_namespace(in_lean_namespace), m_name(n), m_arity(arity) {}
};

optional<extern_fn> get_builtin(name const & n);

enum native_compiler_mode { JIT, AOT };
void native_compile(environment const & env, buffer<pair<name, expr>> & procs, native_compiler_mode & mode);
void native_compile_binary(environment const & env, declaration const & d);
void native_compile_module(environment const & env, buffer<declaration> decls);
void native_compile_module(environment const & env);
// void native_aot_compile(environment const & env, config & conf, declaration const & main);
// void native_compile_file(environment const & env, config & conf, declaration const & main);
environment set_native_module_path(environment & env, name const & n);
void initialize_native_compiler();
void finalize_native_compiler();
}

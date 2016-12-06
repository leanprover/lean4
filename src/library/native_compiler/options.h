/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch, and Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"

namespace lean {
namespace native {
/** \brief Native compiler configuration object. */
struct config {
    char const * m_native_library_path;
    char const * m_native_include_path;
    char const * m_native_main_fn;
    bool         m_native_emit_dwarf;
    bool         m_native_dynamic;
    char const * m_native_dump;

    config(options const & o);

    void display(std::ostream & os);
};

struct scope_config {
    config * m_old;
    config m_config;
public:
    scope_config(options const & o);
    ~scope_config();
};

config & get_config();

void initialize_options();
void finalize_options();
}}

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include <string>
#include "kernel/environment.h"

namespace lean {
    bool has_extern_attribute(environment const & env, name const & d);
    std::string library_name(environment const & env, name const & d);
    std::string symbol_name(environment const & env, name const & d);
    void initialize_extern_attribute();
    void finalize_extern_attribute();
}

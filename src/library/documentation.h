/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
namespace lean {
environment add_doc_string(environment const & env, name const & n, std::string doc);
optional<std::string> get_doc_string(environment const & env, name const & n);
void initialize_documentation();
void finalize_documentation();
}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
environment add_abbreviation(environment const & env, name const & n, bool parsing_only, bool persistent = true);
bool is_abbreviation(environment const & env, name const & n);
bool is_parsing_only_abbreviation(environment const & env, name const & n);
optional<name> is_abbreviated(environment const & env, expr const & e);
bool contains_abbreviations(environment const & env, expr const & e);
expr expand_abbreviations(environment const & env, expr const & e);
void initialize_abbreviation();
void finalize_abbreviation();
}

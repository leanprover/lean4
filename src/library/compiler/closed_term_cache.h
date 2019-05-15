/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
optional<name> get_closed_term_name(environment const & env, expr const & e);
environment cache_closed_term_name(environment const & env, expr const & e, name const & n);
}

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
optional<name> get_closed_term_name(elab_environment const & env, expr const & e);
elab_environment cache_closed_term_name(elab_environment const & env, expr const & e, name const & n);
}

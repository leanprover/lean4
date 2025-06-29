/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
optional<name> get_export_name_for(elab_environment const & env, name const & n);
inline bool has_export_name(elab_environment const & env, name const & n) { return static_cast<bool>(get_export_name_for(env, n)); }
}

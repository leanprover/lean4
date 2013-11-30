/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include "util/name.h"
namespace lean {
typedef std::unordered_set<name, name_hash, name_eq> name_set;
/**
   \brief Make a name that does not occur in \c s, based on
   the given suggestion.
*/
name mk_unique(name_set const & s, name const & suggestion);
}

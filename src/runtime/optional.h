/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <lean/lean.h>
#include <optional>
#include "runtime/debug.h"

namespace lean {
// Alias for backwards-compatibility
template <typename T> using optional = std::optional<T>;

template<typename T> optional<T> some(T const & t) { return optional<T>(t); }
template<typename T> optional<T> some(T && t) { return optional<T>(std::forward<T>(t)); }
}

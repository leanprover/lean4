/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdlib>
#include <lean/lean.h>

namespace lean {
#if defined(LEAN_USE_SPLIT_STACK)
// If we are using split stacks, we don't need to check anything
inline void check_stack(char const * ) { }
inline size_t get_stack_size(bool ) { return 8192*1024; }
inline void save_stack_info(bool = true) {}
inline size_t get_used_stack_size() { return 0; }
inline size_t get_available_stack_size() { return 8192*1024; }
#else
LEAN_EXPORT size_t get_stack_size(bool main);
LEAN_EXPORT void save_stack_info(bool main = true);
LEAN_EXPORT size_t get_used_stack_size();
LEAN_EXPORT size_t get_available_stack_size();
/**
   \brief Throw an exception if the amount of available stack space is low.

   \remark The optional argument \c component_name is used to inform the
   user which module is the potential offender.
*/
LEAN_EXPORT void check_stack(char const * component_name);
#endif

}

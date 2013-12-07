/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
size_t get_stack_size(bool main);
void save_stack_info(bool main = true);
size_t get_used_stack_size();
size_t get_available_stack_size();
/**
   \brief Throw an exception if the amount of available stack space is low.

   \remark The optional argument \c component_name is used to inform the
   user which module is the potential offender.
*/
void check_stack(char const * component_name);
}

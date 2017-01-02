/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
vm_obj caching_user_attribute_get_cache(vm_obj const &, vm_obj const & vm_attr, vm_obj const & vm_s);
void initialize_user_attribute();
void finalize_user_attribute();
}

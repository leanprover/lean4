/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
pos_info to_pos_info(vm_obj const & o);
vm_obj to_obj(pos_info p);
}

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "library/task_queue.h"

namespace lean {

bool execute_task_with_scopes(generic_task_result_cell * task);

}

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_int.h"
#include "library/vm/vm_aux.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_rb_map.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_pexpr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_exceptional.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_task.h"
#include "library/vm/vm_parser.h"
#include "library/vm/vm_array.h"
#include "library/vm/vm_string.h"

namespace lean {
void initialize_vm_core_module() {
    initialize_vm_core();
    initialize_vm_nat();
    initialize_vm_int();
    initialize_vm_aux();
    initialize_vm_io();
    initialize_vm_name();
    initialize_vm_options();
    initialize_vm_format();
    initialize_vm_rb_map();
    initialize_vm_level();
    initialize_vm_expr();
    initialize_vm_pexpr();
    initialize_vm_list();
    initialize_vm_exceptional();
    initialize_vm_task();
    initialize_vm_declaration();
    initialize_vm_environment();
    initialize_vm_parser();
    initialize_vm_array();
    initialize_vm_string();
}

void finalize_vm_core_module() {
    finalize_vm_string();
    finalize_vm_array();
    finalize_vm_parser();
    finalize_vm_environment();
    finalize_vm_declaration();
    finalize_vm_task();
    finalize_vm_exceptional();
    finalize_vm_list();
    finalize_vm_pexpr();
    finalize_vm_expr();
    finalize_vm_level();
    finalize_vm_rb_map();
    finalize_vm_format();
    finalize_vm_options();
    finalize_vm_name();
    finalize_vm_io();
    finalize_vm_aux();
    finalize_vm_int();
    finalize_vm_nat();
    finalize_vm_core();
}

void initialize_vm_module() {
    initialize_vm();
    initialize_vm_expr_builtin_idxs();
    initialize_vm_exceptional_builtin_idxs();
    initialize_vm_format_builtin_idxs();
    initialize_vm_array_builtin_idxs();
}
void finalize_vm_module() {
    finalize_vm();
}
}

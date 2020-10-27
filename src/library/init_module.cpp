/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/constants.h"
#include "library/class.h"
#include "library/num.h"
#include "library/annotation.h"
#include "library/protected.h"
#include "library/io_state.h"
#include "library/idx_metavar.h"
#include "library/placeholder.h"
#include "library/print.h"
#include "library/util.h"
#include "library/pp_options.h"
#include "library/type_context.h"
#include "library/local_context.h"
#include "library/metavar_context.h"
#include "library/check.h"
#include "library/profiling.h"
#include "library/time_task.h"
#include "library/formatter.h"
#include "library/pos_info_provider.h"

namespace lean {
void initialize_library_core_module() {
    initialize_pos_info_provider();
    initialize_formatter();
    initialize_constants();
    initialize_profiling();
    initialize_trace();
}

void finalize_library_core_module() {
    finalize_trace();
    finalize_profiling();
    finalize_constants();
    finalize_formatter();
    finalize_pos_info_provider();
}

void initialize_library_module() {
    initialize_local_context();
    initialize_metavar_context();
    initialize_print();
    initialize_placeholder();
    initialize_idx_metavar();
    initialize_io_state();
    initialize_num();
    initialize_annotation();
    initialize_class();
    initialize_library_util();
    initialize_pp_options();
    initialize_type_context();
    initialize_check();
    initialize_time_task();
}

void finalize_library_module() {
    finalize_time_task();
    finalize_check();
    finalize_type_context();
    finalize_pp_options();
    finalize_library_util();
    finalize_class();
    finalize_annotation();
    finalize_num();
    finalize_io_state();
    finalize_idx_metavar();
    finalize_placeholder();
    finalize_print();
    finalize_metavar_context();
    finalize_local_context();
}
}

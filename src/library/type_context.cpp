/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <lean/interrupt.h>
#include <lean/flet.h>
#include "util/option_declarations.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/quot.h"
#include "kernel/inductive.h"
#include "library/trace.h"
#include "library/class.h"
#include "library/pp_options.h"
#include "library/annotation.h"
#include "library/reducible.h"
#include "library/suffixes.h"
#include "library/constants.h"
#include "library/exception.h"
#include "library/type_context.h"
#include "library/locals.h"
#include "library/aux_recursors.h"
#include "library/num.h"
#include "library/time_task.h"

namespace lean {

/* =====================
   type_context_old
   ===================== */

type_context_old::type_context_old(environment const & env, options const &, transparency_mode):
    m_env(env) {
}

type_context_old::~type_context_old() {
}

void initialize_type_context() {
}

void finalize_type_context() {
}
}

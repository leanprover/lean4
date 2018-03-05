/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "library/vm/vm_io.h"
#include "library/type_context.h"
#include "library/vm/vm.h"
#include "library/constants.h"
#include <string>
#include <vector>

namespace lean {

class eval_helper {
    environment        m_env;
    options            m_opts;
    type_context_old       m_tc;
    buffer<vm_obj>     m_args;
    vm_state           m_vms;
    vm_state::profiler m_prof;
    name               m_fn;
    expr               m_ty;
    unsigned           m_arity;

public:
    eval_helper(environment const & env, options const & opts, name const & fn);

    vm_obj invoke_fn();

    expr const & get_type() const { return m_ty; }
    vm_state::profiler & get_profiler() { return m_prof; }

    optional<vm_obj> try_exec_io();
    optional<vm_obj> try_exec_tac();
    optional<vm_obj> try_exec();
};

}

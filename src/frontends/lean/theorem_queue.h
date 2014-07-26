/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "util/worker_queue.h"
#include "kernel/environment.h"
#include "frontends/lean/local_decls.h"

namespace lean {
class parser;
typedef local_decls<level>  local_level_decls;
class theorem_queue {
    parser & m_parser;
    worker_queue<certified_declaration> m_queue;
public:
    theorem_queue(parser & p, unsigned num_threads);
    void add(environment const & env, name const & n, level_param_names const & ls, local_level_decls const & lls,
             expr const & t, expr const & v);
    std::vector<certified_declaration> const & join();
    void interrupt();
    bool done() const;
};
}

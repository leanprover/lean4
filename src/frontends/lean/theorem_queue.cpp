/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "kernel/type_checker.h"
#include "frontends/lean/theorem_queue.h"
#include "frontends/lean/parser.h"

namespace lean {
theorem_queue::theorem_queue(parser & p, unsigned num_threads):m_parser(p), m_queue(num_threads, []() { enable_expr_caching(false); }) {}
void theorem_queue::add(environment const & env, name const & n, level_param_names const & ls, local_level_decls const & lls,
                        expr const & t, expr const & v) {
    m_queue.add([=]() {
            level_param_names new_ls;
            expr type, value;
            std::tie(type, value, new_ls) = m_parser.elaborate_definition_at(env, lls, n, t, v);
            return check(env, mk_theorem(n, append(ls, new_ls), type, value));
        });
}
std::vector<certified_declaration> const & theorem_queue::join() { return m_queue.join(); }
void theorem_queue::interrupt() { m_queue.interrupt(); }
bool theorem_queue::done() const { return m_queue.done(); }
}

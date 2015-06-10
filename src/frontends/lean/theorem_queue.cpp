/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "library/unfold_macros.h"
#include "library/abbreviation.h"
#include "kernel/type_checker.h"
#include "frontends/lean/theorem_queue.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"

namespace lean {
void theorem_queue::init_queue() {
    m_queue.reset(new worker_queue<certified_declaration>(m_num_threads, []() { enable_expr_caching(false); }));
}
void theorem_queue::consume() {
    for (auto const & c : m_queue->join())
        m_ready.push_back(c);
    init_queue();
}
theorem_queue::theorem_queue(parser & p, unsigned num_threads):m_parser(p), m_num_threads(num_threads) {
    init_queue();
}
void theorem_queue::add(environment const & env, name const & n, level_param_names const & ls, local_level_decls const & lls,
                        expr const & t, expr const & v) {
    m_queue->add([=]() {
            level_param_names new_ls;
            expr type, value;
            std::tie(type, value, new_ls) = m_parser.elaborate_definition_at(env, lls, n, t, v);
            new_ls = append(ls, new_ls);
            value  = postprocess(env, value);
            auto r = check(env, mk_theorem(env, n, new_ls, type, value));
            m_parser.cache_definition(n, t, v, new_ls, type, value);
            return r;
        });
}
void theorem_queue::add(certified_declaration const & c) {
    m_ready.push_back(c);
}
void theorem_queue::for_each(std::function<void(certified_declaration const & c)> const & fn) {
    consume();
    for (auto const & c : m_ready)
        fn(c);
}
void theorem_queue::join() { m_queue->join(); }
void theorem_queue::interrupt() { m_queue->interrupt(); }
bool theorem_queue::done() const { return m_queue->done(); }
}

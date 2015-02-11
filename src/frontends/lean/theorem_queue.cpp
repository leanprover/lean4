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

namespace lean {
theorem_queue::theorem_queue(parser & p, unsigned num_threads):m_parser(p), m_queue(num_threads, []() { enable_expr_caching(false); }) {}
void theorem_queue::add(environment const & env, name const & n, level_param_names const & ls, local_level_decls const & lls,
                        expr const & t, expr const & v) {
    m_queue.add([=]() {
            level_param_names new_ls;
            expr type, value;
            bool is_opaque = true; // theorems are always opaque
            std::tie(type, value, new_ls) = m_parser.elaborate_definition_at(env, lls, n, t, v, is_opaque);
            new_ls = append(ls, new_ls);
            value  = expand_abbreviations(env, unfold_untrusted_macros(env, value));
            auto r = check(env, mk_theorem(n, new_ls, type, value));
            m_parser.cache_definition(n, t, v, new_ls, type, value);
            return r;
        });
}
std::vector<certified_declaration> const & theorem_queue::join() { return m_queue.join(); }
void theorem_queue::interrupt() { m_queue.interrupt(); }
bool theorem_queue::done() const { return m_queue.done(); }
}

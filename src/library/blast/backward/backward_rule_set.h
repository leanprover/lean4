/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"
#include "library/head_map.h"
#include "library/io_state_stream.h"
#include "library/blast/gexpr.h"
#include <vector>

#ifndef LEAN_BACKWARD_DEFAULT_PRIORITY
#define LEAN_BACKWARD_DEFAULT_PRIORITY 1000
#endif

namespace lean {
namespace blast {

class backward_rule {
    name            m_id;
    gexpr           m_proof;
    unsigned        m_priority;

public:
    backward_rule(name const & id, gexpr const & proof, unsigned priority):
        m_id(id), m_proof(proof), m_priority(priority) {}

    name const & get_id() const { return m_id; }
    gexpr const & get_proof() const { return m_proof; }
    unsigned get_priority() const { return m_priority; }
};

bool operator==(backward_rule const & r1, backward_rule const & r2);
inline bool operator!=(backward_rule const & r1, backward_rule const & r2) { return !operator==(r1, r2); }

struct backward_rule_prio_fn { unsigned operator()(backward_rule const & r) const { return r.get_priority(); } };

class backward_rule_set {
    head_map_prio<backward_rule, backward_rule_prio_fn> m_set;

public:
    void insert(type_context & tctx, name const & id, gexpr const & proof, expr const & thm, unsigned prio);
    void insert(type_context & tctx, name const & name, unsigned prio);
    void erase(name_set const & ids);
    void erase(name const & id);
    void for_each(std::function<void(head_index const & h, backward_rule const & r)> const & fn) const;
    list<gexpr> find(head_index const & h) const;
};


void initialize_backward_rule_set();
void finalize_backward_rule_set();
}

environment add_backward_rule(environment const & env, name const & n, unsigned priority, name const & ns, bool persistent);

/** \brief Return true if \c n is an active backward rule in \c env */
bool is_backward_rule(environment const & env, name const & n);

/** \brief Get current backward rule set */
blast::backward_rule_set get_backward_rule_set(environment const & env);
/** \brief Get backward rule set in the given namespace. */
blast::backward_rule_set get_backward_rule_sets(environment const & env, options const & o, name const & ns);

io_state_stream const & operator<<(io_state_stream const & out, blast::backward_rule_set const & r);

}

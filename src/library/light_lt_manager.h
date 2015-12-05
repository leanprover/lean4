/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "library/io_state_stream.h"
#include "util/name_map.h"

namespace lean {

typedef name_map<unsigned> light_rule_set;

environment add_light_rule(environment const & env, name const & id, unsigned light_arg, name const & ns, bool persistent);
optional<unsigned> is_light_rule(environment const & env, name const & n);
light_rule_set get_light_rule_set(environment const & env);
light_rule_set get_light_rule_set(environment const & env, io_state const & ios, name const & ns);

io_state_stream const & operator<<(io_state_stream const & out, light_rule_set const & r);

void initialize_light_rule_set();
void finalize_light_rule_set();

class light_lt_manager {
    light_rule_set m_lrs;
    expr_map<unsigned> m_weight_cache;
    unsigned get_weight_core(expr const & e);
    unsigned get_weight(expr const & e);

public:
    light_lt_manager(environment const & env): m_lrs(get_light_rule_set(env)) {}
    bool is_lt(expr const & a, expr const & b);
};

}

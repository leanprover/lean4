/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include <utility>
#include <vector>
#include "used_defs.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {
struct used_defs {
    name_set m_used_names;
    std::vector<name> m_names_to_process;
    environment const & m_env;
    std::function<void(declaration const &)> m_action;

    // Need a stack and a HashSet
    // Rough algorithm
    // For each name, check to see if its
    // in the set, if not push it on to the stack,
    // when done processing the main fucntion,
    // invoke this procedure with the first item
    // from the stack, and repeat until the stack
    // is empty.
    used_defs(environment const & env, std::function<void(declaration const &)>);
    void names_in_decl(declaration const & d);
    void names_in_expr(expr const & e);
    void names_in_preprocessed_body(expr const & e);
    void add_name(name const & n);
    void empty_stack();
    bool stack_is_empty() {
        return m_names_to_process.empty();
    }
};
}

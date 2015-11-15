/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/action_result.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
/** Generic strategy for synthesizing proofs using the blast framework.
    There are two main configuration options:

    1- Preprocessing (preprocess method)
    2- Next action to be performed (next_action method)
 */
class strategy {
    config   m_config;
    unsigned m_init_num_choices;
    optional<expr> invoke_preprocess();
protected:
    virtual optional<expr> preprocess() = 0;
    virtual action_result next_action() = 0;

    void display_msg(char const * msg);
    void display_action(char const * name);
    void display();
    void display_if(action_result r);

    action_result next_branch(expr pr);
    optional<expr> search_upto(unsigned depth);
    optional<expr> search();
public:
    strategy();
    optional<expr> operator()() { return search(); }
};
}}

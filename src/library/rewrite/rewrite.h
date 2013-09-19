/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once

namespace lean {

class theorem_rw {
private:
    expr const & thm_t;
    expr const & thm_v;
    unsigned num_args;

public:
    theorem_rw(expr const & t, expr const & v);
    void operator()(context & ctx, expr const & t);
};
}

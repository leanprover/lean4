/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "frontends/lean/choice.h"

namespace lean {
static name * g_choice      = nullptr;

/*
  `choice`s will be implemented using syntax objects in Lean4.
  This is a temporary hack to keep the Lean3 frontend alive.
*/

expr mk_choice(unsigned num_es, expr const * es) {
    lean_assert(num_es > 0);
    if (num_es == 1)
        return es[0];
    expr r     = es[num_es - 1];
    unsigned i = num_es - 1;
    while (i > 0) {
        --i;
        r = mk_app(es[i], r);
    }
    kvmap m = set_nat(kvmap(), *g_choice, nat(num_es));
    r = mk_mdata(m, r);
    lean_assert(get_num_choices(r) == num_es);
    return r;
}

void initialize_choice() {
    g_choice      = new name("choice");
}

void finalize_choice() {
    delete g_choice;
}

bool is_choice(expr const & e) {
    return is_mdata(e) && get_nat(mdata_data(e), *g_choice);
}

unsigned get_num_choices(expr const & e) {
    lean_assert(is_choice(e));
    return get_nat(mdata_data(e), *g_choice)->get_small_value();
}

static void get_choices(expr const & e, buffer<expr> & r) {
    lean_assert(is_choice(e));
    expr it    = mdata_expr(e);
    unsigned i = get_nat(mdata_data(e), *g_choice)->get_small_value();
    while (i > 1) {
        --i;
        lean_assert(is_app(it));
        r.push_back(app_fn(it));
        it = app_arg(it);
    }
    r.push_back(it);
}

expr get_choice(expr const & e, unsigned i) {
    buffer<expr> choices;
    get_choices(e, choices);
    return choices[i];
}
}

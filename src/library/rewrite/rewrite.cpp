/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "kernel/abstract.h"
#include "kernel/builtin.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "library/printer.h"
#include "library/rewrite/fo_match.h"
#include "library/rewrite/rewrite.h"

// Term Rewriting
// ORELSE
// APP_RW
// LAMBDA_RW
// PI_RW
// LET_RW
// DEPTH_RW
// THEOREM2RW
// TRIVIAL_RW
// FORALL
// FAIL
// FAIL_IF

using std::cout;
using std::endl;

namespace lean {

theorem_rw::theorem_rw(expr const & t, expr const & v)
    : thm_t(t), thm_v(v), num_args(0) {
    cout << "================= Theorem Rewrite Constructor Start ===================" << endl;
    cout << "Type = " << thm_t << endl;
    cout << "Body = " << thm_v << endl;

    // We expect the theorem is in the form of
    // Pi (x_1 : t_1 ... x_n : t_n), t = s
    expr tmp = t;
    while (is_pi(tmp)) {
        tmp = abst_body(tmp);
        num_args++;
    }
    if (!is_eq(tmp)) {
        cout << "Theorem " << t << " is not in the form of "
                  << "Pi (x_1 : t_1 ... x_n : t_n), t = s" << endl;
    }
    cout << "OK. Number of Arg = " << num_args << endl;
    cout << "================= Theorem Rewrite Constructor END ===================" << endl;
}

void theorem_rw::operator()(context & ctx, expr const & t) {
    cout << "================= Theorem Rewrite () START ===================" << endl;
    cout << "Context = " << ctx << endl;
    cout << "Term = " << t << endl;
    expr tmp = thm_t;
    while (is_pi(tmp)) {
        tmp = abst_body(tmp);
        num_args++;
    }
    if (!is_eq(tmp)) {
        cout << "Theorem " << t << " is not in the form of "
                  << "Pi (x_1 : t_1 ... x_n : t_n), t = s" << endl;
    }
    expr const & lhs = eq_lhs(tmp);
    expr const & rhs = eq_rhs(tmp);
    fo_match fm;
    subst_map s;
    fm.match(lhs, t, 0, s);
    // apply s to rhs

    cout << "================= Theorem Rewrite () END ===================" << endl;
}

}

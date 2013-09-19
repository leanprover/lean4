/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <iostream>
#include "kernel/context.h"
#include "kernel/environment.h"
#include "library/printer.h"
#include "library/rewrite/fo_match.h"

namespace lean {

/**
   \brief Format

   uses `sexpr` as an internal representation.

   nil                    = ["NIL"]
   text         s         = ("TEXT"  . s)
   choice       f1 f2     = ("CHOICE"  f1 . f2)
   compose      f1 ... fn = ["COMPOSE" f1 ... fn]
   line                   = ["LINE"]
   nest         n  f      = ("NEST" n . f)
   highlight    c  f      = ("HIGHLIGHT" c . f)
*/

class theorem_rw {
private:
    expr const & thm_t;
    expr const & thm_v;
    unsigned num_args;
public:
    theorem_rw(expr const & t, expr const & v)
        : thm_t(t), thm_v(v), num_args(0) {
        std::cout << "Theorem_Rewrite "
                  << "(" << thm_v << " : " << thm_t << ")"
                  << std::endl;
        // We expect the theorem is in the form of
        // Pi (x_1 : t_1 ... x_n : t_n), t = s
        expr tmp = t;
        while (is_pi(tmp)) {
            tmp = abst_body(tmp);
            num_args++;
        }
        if (!is_eq(tmp)) {
            std::cout << "Theorem " << t << " is not in the form of "
                      << "Pi (x_1 : t_1 ... x_n : t_n), t = s" << std::endl;
        }
        std::cout << "Theorem " << t << " is OK. Number of Arg = " << num_args << std::endl;
    }

    void operator()(context & ctx, expr const & t) {
        std::cout << "Theorem_Rewrite: ("
                  << "Context : " << ctx
                  << ", Term : " << t
                  << ")" << std::endl;
        fo_match fm;
        subst_map s;
        fm.match(ctx, thm_t, t, s);
    }
};
}

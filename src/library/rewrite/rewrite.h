/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <utility>
#include "util/exception.h"

namespace lean {

class rewrite_exception : public exception {
};

class rewrite {
public:
    virtual std::pair<expr, expr> operator()(context & ctx, expr const & v, expr const & t) const = 0;
};

class theorem_rewrite : public rewrite {
private:
    expr const & thm_type;
    expr const & thm_body;
    expr pattern;
    expr rhs;
    unsigned num_args;

public:
    theorem_rewrite(expr const & type, expr const & body);
    std::pair<expr, expr> operator()(context & ctx, expr const & v, expr const & t) const throw(rewrite_exception);
};

class orelse_rewrite : public rewrite {
private:
    rewrite const & rewrite1;
    rewrite const & rewrite2;
public:
    orelse_rewrite(rewrite const & rw1, rewrite const & rw2) :
        rewrite1(rw1), rewrite2(rw2) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, expr const & t) const throw(rewrite_exception);
};

class then_rewrite : public rewrite {
private:
    rewrite const & rewrite1;
    rewrite const & rewrite2;
public:
    then_rewrite(rewrite const & rw1, rewrite const & rw2) :
        rewrite1(rw1), rewrite2(rw2) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, expr const & t) const throw(rewrite_exception);
};

class fail_rewrite : public rewrite {
public:
    std::pair<expr, expr> operator()(context &, expr const &) const throw(rewrite_exception) {
        throw rewrite_exception();
    }
};
}

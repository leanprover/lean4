/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <utility>
#include "util/exception.h"
#include "kernel/environment.h"

// Term Rewriting
// APP_RW
// LAMBDA_RW
// PI_RW
// LET_RW
// DEPTH_RW
// TRIVIAL_RW
// FORALL
// FAIL
// FAIL_IF

namespace lean {

class rewrite_exception : public exception {
};

class rewrite {
public:
    virtual std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const = 0;
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
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class orelse_rewrite : public rewrite {
private:
    rewrite const & rw1;
    rewrite const & rw2;
public:
    orelse_rewrite(rewrite const & rw_1, rewrite const & rw_2) :
        rw1(rw_1), rw2(rw_2) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class then_rewrite : public rewrite {
private:
    rewrite const & rw1;
    rewrite const & rw2;
public:
    then_rewrite(rewrite const & rw_1, rewrite const & rw_2) :
        rw1(rw_1), rw2(rw_2) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class app_rewrite : public rewrite {
private:
    rewrite const & rw;
public:
    app_rewrite(rewrite const & rw_) :
        rw(rw_) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class lambda_rewrite : public rewrite {
private:
    rewrite const & rw;
public:
    lambda_rewrite(rewrite const & rw_) :
        rw(rw_) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class pi_rewrite : public rewrite {
private:
    rewrite const & rw;
public:
    pi_rewrite(rewrite const & rw_) :
        rw(rw_) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class let_rewrite : public rewrite {
private:
    rewrite const & rw;
public:
    let_rewrite(rewrite const & rw_) :
        rw(rw_) { }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};


class fail_rewrite : public rewrite {
public:
    std::pair<expr, expr> operator()(context &, expr const &) const throw(rewrite_exception) {
        throw rewrite_exception();
    }
};
}

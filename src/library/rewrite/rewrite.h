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

enum class rewrite_kind { Theorem, OrElse, Then, App, Lambda, Pi, Let };

class rewrite;

class rewrite_cell {
protected:
    rewrite_kind m_kind;
    MK_LEAN_RC();
    void dealloc();
public:
    rewrite_cell(rewrite_kind k);
    virtual ~rewrite_cell();
    rewrite_kind kind() const { return m_kind; }
//    unsigned hash() const { return m_hash; }
    virtual std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception) = 0;
};

class rewrite {
private:
    rewrite_cell * m_ptr;
public:
    explicit rewrite(rewrite_cell * ptr):m_ptr(ptr) {}
    rewrite():m_ptr(nullptr) {}
    rewrite(rewrite const & r):m_ptr(r.m_ptr) {
        if (m_ptr) m_ptr->inc_ref();
    }
    rewrite(rewrite && r):m_ptr(r.m_ptr) { r.m_ptr = nullptr; }
    ~rewrite() { if (m_ptr) m_ptr->dec_ref(); }
    void release() { if (m_ptr) m_ptr->dec_ref(); m_ptr = nullptr; }
    friend void swap(rewrite & a, rewrite & b) { std::swap(a.m_ptr, b.m_ptr); }
    rewrite_kind kind() const { return m_ptr->kind(); }
    rewrite & operator=(rewrite const & s) { LEAN_COPY_REF(rewrite, s); }
    rewrite & operator=(rewrite && s) { LEAN_MOVE_REF(rewrite, s); }
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const {
        return (*m_ptr)(ctx, v, env);
    }
};

class theorem_rewrite_cell : public rewrite_cell {
private:
    expr const & m_type;
    expr const & m_body;
    expr m_pattern;
    expr m_rhs;
    unsigned m_num_args;

public:
    theorem_rewrite_cell(expr const & type, expr const & body);
    ~theorem_rewrite_cell();
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class orelse_rewrite_cell : public rewrite_cell {
private:
    rewrite m_rw1;
    rewrite m_rw2;
public:
    orelse_rewrite_cell(rewrite const & rw1, rewrite const & rw2);
    ~orelse_rewrite_cell();
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class then_rewrite_cell : public rewrite_cell {
private:
    rewrite m_rw1;
    rewrite m_rw2;
public:
    then_rewrite_cell(rewrite const & rw1, rewrite const & rw2);
    ~then_rewrite_cell();
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class app_rewrite_cell : public rewrite_cell {
private:
    rewrite m_rw;
public:
    app_rewrite_cell(rewrite const & rw);
    ~app_rewrite_cell();
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class lambda_rewrite_cell : public rewrite_cell {
private:
    rewrite m_rw;
public:
    lambda_rewrite_cell(rewrite const & rw);
    ~lambda_rewrite_cell();
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class pi_rewrite_cell : public rewrite_cell {
private:
    rewrite m_rw;
public:
    pi_rewrite_cell(rewrite const & rw);
    ~pi_rewrite_cell();
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class let_rewrite_cell : public rewrite_cell {
private:
    rewrite m_rw;
public:
    let_rewrite_cell(rewrite const & rw);
    ~let_rewrite_cell();
    std::pair<expr, expr> operator()(context & ctx, expr const & v, environment const & env) const throw(rewrite_exception);
};

class fail_rewrite_cell : public rewrite_cell {
public:
    fail_rewrite_cell(rewrite const & rw1, rewrite const & rw2);
    std::pair<expr, expr> operator()(context &, expr const &) const throw(rewrite_exception) {
        throw rewrite_exception();
    }
};

rewrite mk_theorem_rewrite(expr const & type, expr const & body);
rewrite mk_then_rewrite(rewrite const & rw1, rewrite const & rw2);
rewrite mk_orelse_rewrite(rewrite const & rw1, rewrite const & rw2);
rewrite mk_app_rewrite(rewrite const & rw);
rewrite mk_lambda_rewrite(rewrite const & rw);
rewrite mk_pi_rewrite(rewrite const & rw);
rewrite mk_let_rewrite(rewrite const & rw);
rewrite mk_fail_rewrite();
}

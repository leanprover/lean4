/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <utility>
#include <algorithm>
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

class rewriter_exception : public exception {
};

enum class rewriter_kind {Theorem, OrElse, Then, App, Lambda, Pi, Let, Fail, Success, Repeat};

class rewriter;

class rewriter_cell {
protected:
    rewriter_kind m_kind;
    MK_LEAN_RC();
    void dealloc();
public:
    rewriter_cell(rewriter_kind k);
    virtual ~rewriter_cell();
    rewriter_kind kind() const { return m_kind; }
//    unsigned hash() const { return m_hash; }
    virtual std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) = 0;
};

class rewriter {
private:
    rewriter_cell * m_ptr;
public:
    explicit rewriter(rewriter_cell * ptr):m_ptr(ptr) {}
    rewriter():m_ptr(nullptr) {}
    rewriter(rewriter const & r):m_ptr(r.m_ptr) {
        if (m_ptr) m_ptr->inc_ref();
    }
    rewriter(rewriter && r):m_ptr(r.m_ptr) { r.m_ptr = nullptr; }
    ~rewriter() { if (m_ptr) m_ptr->dec_ref(); }
    void release() { if (m_ptr) m_ptr->dec_ref(); m_ptr = nullptr; }
    friend void swap(rewriter & a, rewriter & b) { std::swap(a.m_ptr, b.m_ptr); }
    rewriter_kind kind() const { return m_ptr->kind(); }
    rewriter & operator=(rewriter const & s) { LEAN_COPY_REF(rewriter, s); }
    rewriter & operator=(rewriter && s) { LEAN_MOVE_REF(rewriter, s); }
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const {
        return (*m_ptr)(env, ctx, v);
    }
};

class theorem_rewriter_cell : public rewriter_cell {
private:
    expr const & m_type;
    expr const & m_body;
    expr m_pattern;
    expr m_rhs;
    unsigned m_num_args;

public:
    theorem_rewriter_cell(expr const & type, expr const & body);
    ~theorem_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class orelse_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
public:
    orelse_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    orelse_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~orelse_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class then_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
public:
    then_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    then_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~then_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class app_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
public:
    app_rewriter_cell(rewriter const & rw);
    ~app_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class lambda_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
public:
    lambda_rewriter_cell(rewriter const & rw);
    ~lambda_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class pi_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
public:
    pi_rewriter_cell(rewriter const & rw);
    ~pi_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class let_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
public:
    let_rewriter_cell(rewriter const & rw);
    ~let_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class fail_rewriter_cell : public rewriter_cell {
public:
    fail_rewriter_cell();
    ~fail_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class success_rewriter_cell : public rewriter_cell {
public:
    success_rewriter_cell();
    ~success_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class repeat_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
public:
    repeat_rewriter_cell(rewriter const & rw);
    ~repeat_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

rewriter mk_theorem_rewriter(expr const & type, expr const & body);
rewriter mk_then_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_then_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_orelse_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_orelse_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_app_rewriter(rewriter const & rw);
rewriter mk_lambda_rewriter(rewriter const & rw);
rewriter mk_pi_rewriter(rewriter const & rw);
rewriter mk_let_rewriter(rewriter const & rw);
rewriter mk_fail_rewriter();
rewriter mk_success_rewriter();
rewriter mk_repeat_rewriter(rewriter const & rw);
}

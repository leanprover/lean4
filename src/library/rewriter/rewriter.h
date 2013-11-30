/*
Copyright (c) 2013 Microsoft Corporation.
Copyright (c) 2013 Carnegie Mellon University.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <utility>
#include <algorithm>
#include "util/exception.h"
#include "kernel/environment.h"

// TODO(soonhok)
// FORALL
// FAIL_IF

namespace lean {

class rewriter_exception : public exception {
public:
    virtual exception * clone() const { return new rewriter_exception(); }
    virtual void rethrow() const { throw *this; }
};

enum class rewriter_kind { Theorem, OrElse, Then, Try, App,
        LambdaType, LambdaBody, Lambda,
        PiType, PiBody, Pi,
        LetType, LetValue, LetBody, Let,
        Fail, Success, Repeat, Depth };

class rewriter;

class rewriter_cell {
protected:
    rewriter_kind m_kind;
    MK_LEAN_RC();
    void dealloc();
    virtual std::ostream & display(std::ostream & out) const = 0;
public:
    rewriter_cell(rewriter_kind k);
    virtual ~rewriter_cell();
    rewriter_kind kind() const { return m_kind; }
//    unsigned hash() const { return m_hash; }
    virtual std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception) = 0;
    friend std::ostream & operator<<(std::ostream & out, rewriter_cell const & rw);
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
    friend std::ostream & operator<<(std::ostream & out, rewriter const & rw);
};

class theorem_rewriter_cell : public rewriter_cell {
private:
    expr const & m_type;
    expr const & m_body;
    expr m_pattern;
    expr m_rhs;
    unsigned m_num_args;
    std::ostream & display(std::ostream & out) const;

public:
    theorem_rewriter_cell(expr const & type, expr const & body);
    ~theorem_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class orelse_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
    std::ostream & display(std::ostream & out) const;
public:
    orelse_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    orelse_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~orelse_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class then_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
    std::ostream & display(std::ostream & out) const;
public:
    then_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    then_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~then_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class try_rewriter_cell : public rewriter_cell {
private:
    list<rewriter> m_rwlist;
    std::ostream & display(std::ostream & out) const;
public:
    try_rewriter_cell(rewriter const & rw1, rewriter const & rw2);
    try_rewriter_cell(std::initializer_list<rewriter> const & l);
    ~try_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class app_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    app_rewriter_cell(rewriter const & rw);
    ~app_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class lambda_type_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    lambda_type_rewriter_cell(rewriter const & rw);
    ~lambda_type_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class lambda_body_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    lambda_body_rewriter_cell(rewriter const & rw);
    ~lambda_body_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class lambda_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    lambda_rewriter_cell(rewriter const & rw);
    ~lambda_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class pi_type_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    pi_type_rewriter_cell(rewriter const & rw);
    ~pi_type_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class pi_body_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    pi_body_rewriter_cell(rewriter const & rw);
    ~pi_body_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class pi_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    pi_rewriter_cell(rewriter const & rw);
    ~pi_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};


class let_type_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_type_rewriter_cell(rewriter const & rw);
    ~let_type_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class let_value_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_value_rewriter_cell(rewriter const & rw);
    ~let_value_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class let_body_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_body_rewriter_cell(rewriter const & rw);
    ~let_body_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class let_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    let_rewriter_cell(rewriter const & rw);
    ~let_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class fail_rewriter_cell : public rewriter_cell {
private:
    std::ostream & display(std::ostream & out) const;
public:
    fail_rewriter_cell();
    ~fail_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class success_rewriter_cell : public rewriter_cell {
private:
    std::ostream & display(std::ostream & out) const;
public:
    success_rewriter_cell();
    ~success_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class repeat_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    repeat_rewriter_cell(rewriter const & rw);
    ~repeat_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

class depth_rewriter_cell : public rewriter_cell {
private:
    rewriter m_rw;
    std::ostream & display(std::ostream & out) const;
public:
    depth_rewriter_cell(rewriter const & rw);
    ~depth_rewriter_cell();
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) const throw(rewriter_exception);
};

/** \brief (For debugging) Display the content of this rewriter */
inline std::ostream & operator<<(std::ostream & out, rewriter_cell const & rc) { rc.display(out); return out; }
inline std::ostream & operator<<(std::ostream & out, rewriter const & rw) { out << *(rw.m_ptr); return out; }

rewriter mk_theorem_rewriter(expr const & type, expr const & body);
rewriter mk_then_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_then_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_try_rewriter(rewriter const & rw);
rewriter mk_try_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_try_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_orelse_rewriter(rewriter const & rw1, rewriter const & rw2);
rewriter mk_orelse_rewriter(std::initializer_list<rewriter> const & l);
rewriter mk_app_rewriter(rewriter const & rw);
rewriter mk_lambda_type_rewriter(rewriter const & rw);
rewriter mk_lambda_body_rewriter(rewriter const & rw);
rewriter mk_lambda_rewriter(rewriter const & rw);
rewriter mk_pi_type_rewriter(rewriter const & rw);
rewriter mk_pi_body_rewriter(rewriter const & rw);
rewriter mk_pi_rewriter(rewriter const & rw);
rewriter mk_let_type_rewriter(rewriter const & rw);
rewriter mk_let_value_rewriter(rewriter const & rw);
rewriter mk_let_body_rewriter(rewriter const & rw);
rewriter mk_let_rewriter(rewriter const & rw);
rewriter mk_fail_rewriter();
rewriter mk_success_rewriter();
rewriter mk_repeat_rewriter(rewriter const & rw);
rewriter mk_depth_rewriter(rewriter const & rw);

std::pair<expr, expr> rewrite_lambda_type(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty);
std::pair<expr, expr> rewrite_lambda_body(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_lambda(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_pi_type(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty);
std::pair<expr, expr> rewrite_pi_body(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_pi(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_eq_lhs(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_lhs);
std::pair<expr, expr> rewrite_eq_rhs(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_rhs);
std::pair<expr, expr> rewrite_eq(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_lhs, std::pair<expr, expr> const & result_rhs);
std::pair<expr, expr> rewrite_let_type(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_ty);
std::pair<expr, expr> rewrite_let_value(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_value);
std::pair<expr, expr> rewrite_let_body(environment const & env, context & ctx, expr const & v, std::pair<expr, expr> const & result_body);
std::pair<expr, expr> rewrite_app(environment const & env, context & ctx, expr const & v, buffer<std::pair<expr, expr>> const & results );
}

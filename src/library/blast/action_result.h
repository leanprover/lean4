/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
namespace blast {
/**
   \brief Result produced by actions, proof-steps and choice-point next method.
   There are 3 possible results
   1- Failed:     action/step/next failed.
   2- NewBranch:  a new branch has been created (or updated) in the current state.
   3- Solved(pr): the current branch has been closed with proof pr. */
class action_result {
public:
    enum kind { Failed, NewBranch, Solved };
private:
    kind m_kind;
    expr m_proof;
    action_result(bool b = true):m_kind(b ? NewBranch : Failed) {}
    action_result(expr const & pr):m_kind(Solved), m_proof(pr) {}
public:
    kind get_kind() const { return m_kind; }
    expr get_proof() const { lean_assert(m_kind == Solved); return m_proof; }
    static action_result failed() { return action_result(false); }
    static action_result new_branch() { return action_result(true); }
    static action_result solved(expr const & pr) { return action_result(pr); }
    optional<expr> to_opt_expr() const { return m_kind == Solved ? some_expr(m_proof) : none_expr(); }
};

inline bool failed(action_result const & r) { return r.get_kind() == action_result::Failed; }
inline bool solved(action_result const & r) { return r.get_kind() == action_result::Solved; }
}}

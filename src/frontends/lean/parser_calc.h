/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/list.h"
#include "util/optional.h"
#include "kernel/expr.h"
#include "frontends/lean/parser_types.h"

namespace lean {
class parser_imp;
class operator_info;
/**
   \brief Information for a operator available in the
   calculational proof module. It must have at least two arguments.
   It may have implicit ones. We assume the implicit arguments
   occur in the beginning.
*/
struct op_data {
    expr     m_fn;
    unsigned m_num_args;
    op_data(expr const & f, unsigned n): m_fn(f), m_num_args(n) {}
};

/**
   \brief Information about a transitivity-like proof step.

   The m_fn  function must have at least 5 arguments.
   We assume the implicit ones occur in the beginning.
   The last five are a, b, c and a proof for 'a op1 b' and 'b op2 c'.
   The function m_fn  produces a proof for 'a rop b'.
   The resultant operator must be in the list of supported operators.
*/
struct trans_data {
    expr       m_fn;
    unsigned   m_num_args; // number of arguments of m_fn .
    expr       m_rop;     // resultant operator
    trans_data(expr const & f, unsigned n, expr const & rop):
        m_fn (f), m_num_args(n), m_rop(rop) {
    }
};

/**
   \brief Calculational proof support in the Lean parser.

   It parses expression of the form:

   calc expr op expr : proof1
        ...  op expr : proof2

        ...  op expr : proofn
*/
class calc_proof_parser {
    /**
       \brief List of supported operators in calculational proofs.
    */
    list<op_data> m_supported_operators;

    /**
       \brief Maps to operators to the corresponding transitivity operator.
       For example, the pair (=, =>) maps to

           Theorem EqImpTrans {a b c : Bool} (H1 : a == b) (H2 : b ⇒ c) : a ⇒ c
          := assume Ha, MP H2 (EqMP H1 Ha).
    */
    list<std::tuple<expr, expr, trans_data>> m_trans_ops;
    optional<trans_data> find_trans_data(expr const & op1, expr const & op2) const;
    optional<expr> find_op(operator_info const & op, pos_info const & p) const;
    expr parse_op(parser_imp & imp) const;
public:
    calc_proof_parser();

    bool supports(expr const & op1) const;
    void add_supported_operator(op_data const & op);
    void add_trans_step(expr const & op1, expr const & op2, trans_data const & d);

    expr parse(parser_imp & p) const;
};
}

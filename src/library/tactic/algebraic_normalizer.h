/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/expr_maps.h"
#include "library/type_context.h"
#include "library/head_map.h"

/*
This is currently dead code.
This is a partial attempt to generalize the `ac_manager` and `arith_instance` classes.

It is not clear whether we will have an algebraic normalizer that automatically applies lemmas such
as `left_inv` from
```
@[algebra] class is_left_inv (α : Type u) (op : α → α → α) (inv : out_param $ α → α) (o : out_param α) : Prop :=
(left_inv : ∀ a, op (inv a) a = o)
```

Disadvantage: most of the functionality of the algebraic normalizer is subsumed by AC rewriting.
However, the algebraic normalizer will be able to applies algebraic lemmas more efficiently than a generic
AC rewriting engine based on AC matching.

Advantage: as soon as we have an instance `is_left_inv α op inv o`, the normalizer can apply the lemma.
Moreover, it will apply the lemma modulo other algebraic properties such as is_associative and is_commutative.
The algebraic normalizer would use caches such as the one in `ac_manager` to efficiently identify terms to be simplified.
The AC rewriter (aka simplifier) has to be "fed" with first order lemmas.
For example, we cannot use the following lemma in the simplifier.
```
@[simp] lemma left_inv {α : Type u} {op : α → α → α} {inv : α → α} {o : α} [is_left_inv α op inv o] (a : α) :  op (inv a) a = o
```
There isn't a single symbol in the left-hand-side. We would have to match subterms of our goals with the
higher order term `?op (?inv ?a) ?a` where `?op`, `?inv` and `?a` are metavariables.
So, to be able to use simplifier, whenever we define an instance `[is_left_inv α op inv o]`, we would have to instantiate
lemmas such as `left_inv`, create auxiliary lemmas with these instances and mark them with the `[simp]` attribute.
In principle, this process can be automated with a new tactic.

If we decide to use the AC rewriter to apply lemmas such as left_inv, then the algebraic normalize will perform
only more complex tasks such as "fusion" where the term `k_1 * t + k_2 * t` is simplified into `k * t`, where
`k_1`, `k_2` and `k` are numerals, and `k = k_1 + k_2`.

*/

namespace lean {
struct algebraic_info {
    struct lr_info {
        optional<expr> m_left_proof;
        optional<expr> m_right_proof;
    };

    struct lr_op_info : public lr_info {
        expr m_op;
    };

    struct lr_elem_info : public lr_info {
        expr m_elem;
    };

    struct inv_info {
        expr m_inv;
        expr m_o;
        expr m_proof;
    };

    struct cond_inv_info : public inv_info {
        expr m_p;
    };

    expr                     m_op;
    optional<expr>           m_comm;
    optional<expr>           m_assoc;
    optional<expr>           m_idempotent;
    optional<lr_info>        m_cancel;
    optional<lr_elem_info>   m_id;
    optional<lr_elem_info>   m_null;
    optional<lr_op_info>     m_distrib;
    optional<inv_info>       m_left_inv;
    optional<inv_info>       m_right_inv;
    optional<cond_inv_info>  m_cond_left_inv;
    optional<cond_inv_info>  m_cond_right_inv;
};

typedef std::shared_ptr<algebraic_info const> algebraic_info_ref;

class algebraic_info_manager {
public:
    struct data {
        environment                              m_env;
        local_context                            m_lctx;
        name_set                                 m_symbols;
        head_map<pair<expr, algebraic_info_ref>> m_head_info;
        expr_map<algebraic_info_ref>             m_op_info;
    };
    typedef std::shared_ptr<data>                data_ptr;

private:
    type_context_old &                               m_ctx;
    data_ptr                                     m_data;

public:
    algebraic_info_manager(type_context_old & ctx);
    ~algebraic_info_manager();
    type_context_old & ctx() const { return m_ctx; }
    algebraic_info_ref get_info(expr const & op);
};

void initialize_algebraic_normalizer();
void finalize_algebraic_normalizer();
}

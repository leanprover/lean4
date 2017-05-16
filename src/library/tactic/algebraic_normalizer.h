/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/type_context.h"
#include "library/head_map.h"

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
    type_context &                               m_ctx;
    data_ptr                                     m_data;

public:
    algebraic_info_manager(type_context & ctx);
    ~algebraic_info_manager();
    type_context & ctx() const { return m_ctx; }
    algebraic_info_ref get_info(expr const & op);
};

void initialize_algebraic_normalizer();
void finalize_algebraic_normalizer();
}

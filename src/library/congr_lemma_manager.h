/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "library/app_builder.h"
#include "library/fun_info_manager.h"

namespace lean {
class congr_lemma_manager {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    congr_lemma_manager(app_builder & b, fun_info_manager & fm);
    ~congr_lemma_manager();

    enum class congr_arg_kind { Fixed, Eq, Cast };

    class result {
        expr                 m_type;
        expr                 m_proof;
        list<congr_arg_kind> m_arg_kinds;
    public:
        result(expr const & type, expr const & proof, list<congr_arg_kind> const & ks):
            m_type(type), m_proof(proof), m_arg_kinds(ks) {}
        expr const & get_type() const { return m_type; }
        expr const & get_proof() const { return m_proof; }
        list<congr_arg_kind> const & get_arg_kinds() const { return m_arg_kinds; }
    };

    optional<result> mk_congr_simp(expr const & fn);
    optional<result> mk_congr_simp(expr const & fn, unsigned nargs);
};
}
